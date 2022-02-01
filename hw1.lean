/-! # Lean hw 1

This homework will be graded for effort only, on a yes/no basis.  You must upload a file to
Gradescope, but it is fine if you can't solve all the problems.
-/

lemma problem1 {a b : ℤ} (h : a - b = 0) : a = b :=
begin
  add_both_sides(b: ℤ) at h,
  exact_mod_ring h
end

lemma problem2 {a : ℚ} (ha : 3 * a + 1 = 4) : a = 1 :=
begin
  add_both_sides(-1: ℚ) at ha,
  mul_both_sides(1/3: ℚ) at ha,
  exact_mod_ring ha,
end

