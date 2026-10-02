-- Prove2me | solution 1 for CelestialHolography.mobius_mul
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T13:54:05.504672+00:00
-- url     : https://prove2.me/submissions/74e8034e-0bcf-4c67-8441-d063c518253f

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

open CelestialHolography in
theorem solution (M N : Matrix.SpecialLinearGroup (Fin 2) ℂ) (z : ℂ)
    (hN : N 1 0 * z + N 1 1 ≠ 0) (hMN : (M * N) 1 0 * z + (M * N) 1 1 ≠ 0) :
    mobius (M * N) z = mobius M (mobius N z) := by
  have e : ∀ i j, (M * N) i j = M i 0 * N 0 j + M i 1 * N 1 j := by
    intro i j
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  unfold mobius
  rw [e, e] at hMN
  rw [e, e, e, e]
  have hM : M 1 0 * ((N 0 0 * z + N 0 1) / (N 1 0 * z + N 1 1)) + M 1 1 ≠ 0 := by
    have : M 1 0 * ((N 0 0 * z + N 0 1) / (N 1 0 * z + N 1 1)) + M 1 1
        = ((M 1 0 * N 0 0 + M 1 1 * N 1 0) * z + (M 1 0 * N 0 1 + M 1 1 * N 1 1))
          / (N 1 0 * z + N 1 1) := by
      rw [eq_div_iff hN, add_mul, mul_assoc, div_mul_cancel₀ _ hN]
      ring
    rw [this]
    exact div_ne_zero hMN hN
  rw [div_eq_div_iff hMN hM]
  field_simp
  ring
