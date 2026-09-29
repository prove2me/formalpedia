-- Prove2me | solution 1 for EulerMascheroni.Mixed.cyclic_matrix_determinant
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T15:15:22.660035+00:00
-- url     : https://prove2.me/submissions/d3e0dede-4f5d-4a7a-9f84-3f8bb3fc1f17

import Mathlib
set_option autoImplicit false
namespace EulerCyclic
lemma determinant (a b c z : ℂ) (hz : z ≠ 0) :
    Matrix.det (!![a,b,c; -c/z,b+c/z,c; c/z^2-c/z,b+2*c/z-c/z^2,c]) =
      -c^2*(a*z-a+c)/z^2 := by
  simp [Matrix.det_fin_three,Matrix.of_apply]
  field_simp
  <;> ring
lemma at_one (a b c : ℂ) :
    Matrix.det (!![a,b,c; -c,b+c,c; 0,b+c,c]) = -c^3 ∧
    (c ≠ 0 → Matrix.det (!![a,b,c; -c,b+c,c; 0,b+c,c]) ≠ 0) := by
  have h : Matrix.det (!![a,b,c; -c,b+c,c; 0,b+c,c]) = -c^3 := by
    simp [Matrix.det_fin_three,Matrix.of_apply]
    ring
  refine ⟨h,?_⟩
  intro hc
  rw [h]
  exact neg_ne_zero.mpr (pow_ne_zero 3 hc)
end EulerCyclic


theorem solution (a b c z : ℂ) (hz : z ≠ 0) :
    Matrix.det (!![a,b,c; -c/z,b+c/z,c; c/z^2-c/z,b+2*c/z-c/z^2,c]) =
      -c^2*(a*z-a+c)/z^2 ∧
    Matrix.det (!![a,b,c; -c,b+c,c; 0,b+c,c]) = -c^3 ∧
    (c ≠ 0 → Matrix.det (!![a,b,c; -c,b+c,c; 0,b+c,c]) ≠ 0) := by
  exact ⟨EulerCyclic.determinant a b c z hz, EulerCyclic.at_one a b c⟩

#print axioms solution
