-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.norm_lamF_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:47.495804+00:00
-- url     : https://prove2.me/submissions/49aef041-94de-44dd-ab31-bec278f0a28e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_coeff_lamF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_geom_sum_mul_pred
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj


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
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
namespace Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ} {ϖ : K}
    (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) (hϖ : ϖ ^ (p ^ 2 - 1) = (p : K)) (n : ℕ) :
    ‖PowerSeries.coeff n (lamF p ϖ - PowerSeries.X - PowerSeries.X ^ (p ^ 2))‖ ≤ (p : ℝ)⁻¹ := by
  have hp2 := hp.two_le
  have hpR : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.pos)
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact absurd hn hpR.ne
  have hq1 : p ^ 2 ≠ 1 := by nlinarith
  rw [map_sub, map_sub, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, coeff_lamF]
  by_cases h : PowerSeries.coeff n (lgF K p) = 0
  · have h1 : n ≠ 1 := by
      rintro rfl
      have h' := coeff_lgF_pow K hp2 0
      rw [pow_zero, pow_zero, inv_one, h] at h'
      exact zero_ne_one h'
    have h2 : n ≠ p ^ 2 := by
      rintro rfl
      have h' := coeff_lgF_pow K hp2 1
      rw [pow_one, h] at h'
      exact inv_ne_zero (pow_ne_zero 1 hpK) h'.symm
    rw [h, if_neg h1, if_neg h2]
    simp
  · obtain ⟨j, rfl⟩ := coeff_lgF_ne_zero h
    rw [coeff_lgF_pow K hp2 j]
    rcases j with _ | _ | j
    · rw [pow_zero, if_pos rfl, if_neg (Ne.symm hq1)]
      simp
    · rw [zero_add, pow_one, pow_one, hϖ, if_neg hq1, if_pos rfl, mul_inv_cancel₀ hpK]
      simp
    · have h1 : (p ^ 2) ^ (j + 2) ≠ 1 := fun h' =>
        absurd (powq_inj hp2 (h'.trans (pow_zero _).symm)) (by omega)
      have h2 : (p ^ 2) ^ (j + 2) ≠ p ^ 2 := fun h' =>
        absurd (powq_inj hp2 (h'.trans (pow_one _).symm)) (by omega)
      obtain ⟨g, hg, _, hj⟩ := geom_sum_mul_pred (q := p ^ 2) (by nlinarith) (j + 2)
      have hj' := hj (by omega)
      obtain ⟨t, rfl⟩ : ∃ t, g = (j + 2) + (t + 1) := ⟨g - (j + 2) - 1, by omega⟩
      rw [if_neg h1, if_neg h2, sub_zero, sub_zero, hg, Nat.add_sub_cancel, pow_mul, hϖ, pow_add,
        mul_comm ((p : K) ^ (j + 2)), mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hpK), mul_one,
        norm_pow, hn, pow_succ]
      exact mul_le_of_le_one_left hpR.le (pow_le_one₀ hpR.le
        (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)))
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
