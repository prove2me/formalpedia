-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.C_norm_fderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:33.704626+00:00
-- url     : https://prove2.me/submissions/de320cce-cd56-444d-a69c-d612e0064250

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Bl_general_b_fact_second_bis_form_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {f : E → F} {y : E} {δ M : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball y δ)) (hM : ∀ z ∈ ball y δ, ‖f z‖ ≤ M) :
    ‖fderiv ℂ f y‖ ≤ M / δ := by
  first | exact Bl.general_b_fact_second_bis_form.goal1 .. | (apply Bl.general_b_fact_second_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_bis_form.goal1 <;> assumption)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
