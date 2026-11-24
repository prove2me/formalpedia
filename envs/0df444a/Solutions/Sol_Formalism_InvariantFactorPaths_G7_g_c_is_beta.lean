-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.g_c_is_beta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:37:07.509898+00:00
-- url     : https://prove2.me/submissions/3d1877e0-a587-47d1-a15c-60db3a8654ea

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_FrobeniusPartialCoboundaryBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_suppOK_Gser
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_swap_two_g_series
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_scale_of_suppOK
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoefficientSupportCongruences_partial_coboundary_g_series_equiv
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_PhiH_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_add
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_neg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_bd_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_frob_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_DworkIntegrality_int_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_simeqRules
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_simeqRules


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
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)
open CoefficientSupportCongruences
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : GcIsBeta := by
  intro K _ _ _ p σ hU F hF c hc hσσ
  have hp2 : 2 ≤ p := le_of_lt hU.2.1
  have hσc : ‖σ c‖ ≤ 1 := by
    have h1 : ‖σ c - c ^ p‖ ≤ (p : ℝ)⁻¹ := hU.2.2.2.2 c hc
    have h2 : ‖c ^ p‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
    have h3 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ p))
    calc ‖σ c‖ = ‖(σ c - c ^ p) + c ^ p‖ := by rw [sub_add_cancel]
      _ ≤ max ‖σ c - c ^ p‖ ‖c ^ p‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (h1.trans h3) h2
  have hS := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin 2)).1
  refine ⟨?_, partial_coboundary_g_series_equiv hU hF hc hσσ, ?_, ?_⟩
  · intro n hn
    by_contra h
    obtain ⟨h0, h1, -⟩ := suppOK_Gser (K := K) hp2 c (σ c) n h
    omega
  · rw [swap_two_g_series]
    have h := partial_coboundary_g_series_equiv hU hF (c := -σ c) (by rwa [norm_neg]) (by simp [hσσ])
    simpa [hσσ] using h
  · intro ζ hζ
    rw [scale_of_suppOK (suppOK_Gser hp2 c (σ c)) hζ]
    exact hS _
end Formalism.InvariantFactorPaths.G7
