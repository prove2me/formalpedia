-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.height_integral_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:48.109719+00:00
-- url     : https://prove2.me/submissions/97e01932-873b-4fb1-a431-6e0e95a76dc1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CardUnitsZmodPrimeSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : SW_height_integral := by
  intro M f c R hM hc hR
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 3 := ⟨M - 3, by omega⟩
  have hA : 0 < c * R ^ (2 * f) := by positivity
  have hcongr : ∫ t in (0 : ℝ)..(c * R ^ (2 * f)), (R ^ (2 * f) / t) * t ^ (k + 3 - 1) / t
      = ∫ t in (0 : ℝ)..(c * R ^ (2 * f)), R ^ (2 * f) * t ^ k := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro t ht
    rw [Set.uIoc_of_le hA.le] at ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have : k + 3 - 1 = k + 2 := by omega
    rw [this]
    field_simp
    ring
  rw [hcongr, intervalIntegral.integral_const_mul, integral_pow]
  have e1 : k + 3 - 2 = k + 1 := by omega
  have e2 : 2 * f * (k + 3 - 1) = 2 * f + 2 * f * (k + 1) := by
    have : k + 3 - 1 = 1 + (k + 1) := by omega
    rw [this]; ring
  rw [e1, e2, pow_add R, pow_mul R (2 * f) (k + 1), mul_pow]
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hk' : (((k + 3 : ℕ) : ℝ) - 2) = (k : ℝ) + 1 := by push_cast; ring
  rw [hk']
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, sub_zero]
  field_simp
end Formalism.HermitianLattices.GenusMassVolumes
