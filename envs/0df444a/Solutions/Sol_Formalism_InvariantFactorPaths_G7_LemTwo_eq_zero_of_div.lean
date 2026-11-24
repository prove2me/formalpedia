-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemTwo.eq_zero_of_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:08.679795+00:00
-- url     : https://prove2.me/submissions/79730cf4-fec0-46d1-874c-380ae1dae6cd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LemmaTwoOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemTwo
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.LemTwo
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {x : K}
    (h : ∀ N : ℕ, ∃ i, N ≤ i ∧ ‖((p : K) ^ i)⁻¹ * x‖ ≤ 1) : x = 0 := by
  by_contra hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hp1 : ((p : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hxpos hp1
  obtain ⟨i, hi, hle⟩ := h N
  have hpos : (0 : ℝ) < (p : ℝ) ^ i := by positivity
  rw [norm_mul, norm_inv, norm_pow, hnp, inv_pow, inv_inv] at hle
  have h1 : ‖x‖ ≤ ((p : ℝ)⁻¹) ^ i := by
    rw [inv_pow]
    calc ‖x‖ = ((p : ℝ) ^ i)⁻¹ * ((p : ℝ) ^ i * ‖x‖) := by field_simp
      _ ≤ ((p : ℝ) ^ i)⁻¹ * 1 := by gcongr
      _ = ((p : ℝ) ^ i)⁻¹ := mul_one _
  have h2 : ((p : ℝ)⁻¹) ^ i ≤ ((p : ℝ)⁻¹) ^ N := pow_le_pow_of_le_one (by positivity) hp1.le hi
  linarith
end Formalism.InvariantFactorPaths.G7.LemTwo
