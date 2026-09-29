-- Prove2me | solution 1 for DiazModulus.diaz_on_axes_of_hermite_lindemann
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T09:30:50.815744+00:00
-- url     : https://prove2.me/submissions/67fef296-b99b-49c2-8df3-ec88930726ba

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

open DiazModulus in
theorem solution (hHL : HermiteLindemann) (u : ℂ) (hu : u ≠ 0)
    (hax : u.im = 0 ∨ u.re = 0) (hmod : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)) :
    Transcendental ℚ (Complex.exp u) := by
  -- `‖u‖²` is `u * conj u`, and on either axis conjugation acts as `±1`
  have key : ((‖u‖ : ℝ) : ℂ) ^ 2 = u * conj u := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hq : ((‖u‖ : ℝ) : ℂ) ∈ Qbar := mem_Qbar_iff.mpr hmod
  have hsq : u ^ 2 ∈ Qbar := by
    rcases hax with h | h
    · -- real axis: `conj u = u`, so `‖u‖² = u²`
      have hc : conj u = u := Complex.conj_eq_iff_im.mpr h
      have : u ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 := by rw [key, hc]; ring
      rw [this]
      exact pow_mem hq 2
    · -- imaginary axis: `conj u = -u`, so `‖u‖² = -u²`
      have hc : conj u = -u := by
        apply Complex.ext <;> simp [h]
      have : u ^ 2 = -(((‖u‖ : ℝ) : ℂ) ^ 2) := by rw [key, hc]; ring
      rw [this]
      exact neg_mem (pow_mem hq 2)
  exact hHL u hu (IsAlgebraic.of_pow two_pos (mem_Qbar_iff.mp hsq))
