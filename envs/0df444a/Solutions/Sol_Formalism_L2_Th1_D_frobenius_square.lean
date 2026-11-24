-- Prove2me | solution 1 for Formalism.L2.Th1.D.frobenius_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:36:51.690951+00:00
-- url     : https://prove2.me/submissions/153a5242-4e3e-4a29-b7a7-4b67e882d2d1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Lemmata_GeneralBFactUpper_Imports
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Theorems.Thm_Formalism_L2_Th1_D_ip_norm_pow_sub_pow_le
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_frobVar_eq_expand


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (lgF UnrOK frobVar frobVar_eq_expand)
namespace Formalism.L2.Th1.D
theorem _root_.solution : FrobSq := by
  intro K _ _ _ l σ h
  obtain ⟨hl, _, hn, _, hσ⟩ := h
  have hl1 : ((l : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hl.one_le)
  have hball : ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := by
    intro a ha
    have h : σ a = (σ a - a ^ l) + a ^ l := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hσ a ha).trans hl1) ?_)
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha
  refine ⟨⟨hl, ⟨2, by norm_num, rfl⟩, ?_, ?_⟩, hball⟩
  · rw [hn]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl.one_lt)
  · intro a ha
    rw [hn]
    have h : (σ.comp σ) a - a ^ (l ^ 2) =
        (σ (σ a) - (σ a) ^ l) + ((σ a) ^ l - (a ^ l) ^ l) := by
      rw [RingHom.comp_apply, pow_two, pow_mul]
      ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hσ _ (hball a ha)) ?_)
    exact (ip_norm_pow_sub_pow_le (hball a ha)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha) l).trans (hσ a ha)
end Formalism.L2.Th1.D
