-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_gau_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:56.266662+00:00
-- url     : https://prove2.me/submissions/37697494-88ce-4cd9-83a6-10c0bed5a2dc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_isAddHaar_muPi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_norm_sq_le_nsq
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_exp_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (δ : ℝ) (hδ : 0 < δ) :
    Integrable (D_gau d δ) (muPi β (Fin d)) := by
  have := isAddHaar_muPi d β hβ
  have h1 : Integrable (D_gau d 1) (muPi β (Fin d)) := by
    have hfin : (Module.finrank ℝ (Fin d → ℂ) : ℝ) < ((2 * (d + 1) : ℕ) : ℝ) := by
      have : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
        simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
      rw [this]
      exact_mod_cast (by omega : 2 * d < 2 * (d + 1))
    have hint := (integrable_one_add_norm (μ := muPi β (Fin d)) hfin).const_mul
      (2 ^ (d + 1) * ((d + 1).factorial : ℝ) * Real.exp 1)
    refine hint.mono' (D_gau_continuous d 1).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (D_gau_nonneg d 1 x), Real.rpow_neg (by positivity), Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    have h2 : D_gau d 1 x ≤ Real.exp (-‖x‖ ^ 2) := by
      have : D_gau d 1 x = Real.exp (- D_nsq d x) := by simp [D_gau, D_nsq]
      rw [this]
      exact Real.exp_le_exp.2 (neg_le_neg (D_norm_sq_le_nsq d x))
    calc (1 + ‖x‖) ^ (2 * (d + 1)) * D_gau d 1 x ≤ (1 + ‖x‖) ^ (2 * (d + 1)) * Real.exp (-‖x‖ ^ 2) := by gcongr
      _ ≤ _ := D_exp_decay (d + 1) ‖x‖ (norm_nonneg x)
  rw [D_gau_scale d δ hδ.le]
  exact h1.comp_smul (Real.sqrt_pos.2 hδ).ne'
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
