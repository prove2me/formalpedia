-- Prove2me | solution 1 for FiniteEnergyPlane.eq_mul_exp_integral_div_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T22:27:14.961383+00:00
-- url     : https://prove2.me/submissions/6812a808-2e67-440a-92a9-7c7fda9fa85b

import Mathlib



namespace FiniteEnergyPlane

theorem eq_mul_exp_integral_div_of_hasDerivAt_aux {X X' : ℝ → ℂ}
    (hX : ∀ t, HasDerivAt X (X' t) t) (hX' : Continuous X') (h0 : ∀ t, X t ≠ 0) (t : ℝ) :
    X t = X 0 * Complex.exp (∫ s in (0 : ℝ)..t, X' s / X s) := by
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun t => (hX t).continuousAt
  have hq : Continuous fun s => X' s / X s := hX'.div hXc h0
  set W : ℝ → ℂ := fun u => ∫ s in (0 : ℝ)..u, X' s / X s with hWdef
  have hW : ∀ u, HasDerivAt W (X' u / X u) u := fun u =>
    (hq.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hh : ∀ u, HasDerivAt (fun u => X u * Complex.exp (-W u)) 0 u := by
    intro u
    have h1 := (hX u).mul ((hW u).neg.cexp)
    refine h1.congr_deriv ?_
    have hx : X u * (X' u / X u) = X' u := mul_div_cancel₀ _ (h0 u)
    linear_combination (-Complex.exp (-W u)) * hx
  have hconst := is_const_of_deriv_eq_zero (fun u => (hh u).differentiableAt)
    (fun u => (hh u).deriv) t 0
  have hW0 : W 0 = 0 := by simp [hWdef]
  simp only [hW0, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {X X' : ℝ → ℂ}
    (hX : ∀ t, HasDerivAt X (X' t) t) (hX' : Continuous X') (h0 : ∀ t, X t ≠ 0) (t : ℝ) :
    X t = X 0 * Complex.exp (∫ s in (0 : ℝ)..t, X' s / X s) :=
  eq_mul_exp_integral_div_of_hasDerivAt_aux hX hX' h0 t
