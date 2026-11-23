-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit.cof_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:26:38.587961+00:00
-- url     : https://prove2.me/submissions/f118fbbe-4214-4447-a332-a5484e32c7be

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_cofXY_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_first_cofactor_norm_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_G6_rpow_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
theorem _root_.solution (m : ℕ) {δ c ε : ℝ} (hδ : 0 < δ) (hc : 2 ≤ c) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / (2 * ((m : ℝ) + 2))) {t : ℂ} (ht0 : t ≠ 0) (ht1 : ‖t‖ ≤ 1)
    (hts : ((m : ℝ) + 1) ^ (m + 1) * c ^ m * Real.sqrt ‖t‖ ≤ δ ^ (m + 1) / 2)
    (p : XY m) (hx : ∀ k, ‖p.1 k‖ ≤ c) (hxl : ∀ k, δ ≤ ‖p.1 k‖) (hy : ‖p.2‖ ≤ 2 * ‖t‖ ^ (-ε)) :
    δ ^ (m + 1) ≤ ‖∏ k, p.1 k‖ ∧ δ ^ (m + 1) / 2 ≤ ‖cofXY m t p‖ := by
  have htp : 0 < ‖t‖ := norm_pos_iff.2 ht0
  have hT : 1 ≤ ‖t‖ ^ (-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos htp ht1 (by linarith)
  set T := ‖t‖ ^ (-ε) with hTdef
  have hprod : δ ^ (m + 1) ≤ ‖∏ k, p.1 k‖ := by
    rw [norm_prod]
    calc δ ^ (m + 1) = ∏ _k : Fin (m + 1), δ := by simp
      _ ≤ ∏ k, ‖p.1 k‖ := Finset.prod_le_prod (fun _ _ => hδ.le) fun k _ => hxl k
  refine ⟨hprod, ?_⟩
  have hR : 1 ≤ c * T := by nlinarith
  have h1 := first_cofactor_norm_le m t p hR ht1 (fun k => (hx k).trans (by nlinarith)) (hy.trans (by nlinarith))
  have h2 : T ^ m * ‖t‖ ≤ Real.sqrt ‖t‖ := by
    refine le_trans ?_ (G6.rpow_bound m htp ht1 hε)
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hT (by omega)) htp.le
  have h3 : ‖t * cof1XY m t p‖ ≤ δ ^ (m + 1) / 2 := by
    rw [norm_mul]
    calc ‖t‖ * ‖cof1XY m t p‖ ≤ ‖t‖ * (((m : ℝ) + 1) ^ (m + 1) * (c * T) ^ m) :=
          mul_le_mul_of_nonneg_left h1 htp.le
      _ = ((m : ℝ) + 1) ^ (m + 1) * c ^ m * (T ^ m * ‖t‖) := by rw [mul_pow]; ring
      _ ≤ ((m : ℝ) + 1) ^ (m + 1) * c ^ m * Real.sqrt ‖t‖ :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ _ := hts
  have h4 : ‖cof0XY m p‖ = ‖∏ k, p.1 k‖ := by simp [cof0XY, norm_pow]
  have h5 : cof0XY m p = cofXY m t p - t * cof1XY m t p := by rw [cofXY_eq]; ring
  have h6 : ‖cof0XY m p‖ ≤ ‖cofXY m t p‖ + ‖t * cof1XY m t p‖ := by rw [h5]; exact norm_sub_le _ _
  linarith
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Crit
