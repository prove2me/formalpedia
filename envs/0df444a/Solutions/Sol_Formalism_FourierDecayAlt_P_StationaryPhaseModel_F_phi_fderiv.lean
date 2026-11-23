-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:31.398901+00:00
-- url     : https://prove2.me/submissions/3eeec809-e439-438c-a8b7-0748d6d3f568

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_ev
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_hasFDerivAt_Tg

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
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) {x : Fin d → ℂ}
    (hx : x ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4)) (v : Fin d → ℂ) :
    fderiv ℝ (F_phi d r c g) x v = (c * fderiv ℂ g x v).re := by
  have hx2 : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.ball_subset_ball (by linarith) hx
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (F_phi_ev (g := g) hr c hx), (F_hasFDerivAt_Tg hg c hx2).fderiv]
  rfl
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
