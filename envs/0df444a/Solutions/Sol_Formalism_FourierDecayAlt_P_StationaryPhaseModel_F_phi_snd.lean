-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_snd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:41.896484+00:00
-- url     : https://prove2.me/submissions/d317ed4a-4ea3-4c6c-9b74-2733c2084a63

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_T_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_hasFDerivAt_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_fderiv

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
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) (u v : Fin d → ℂ) :
    fderiv ℝ (fderiv ℝ (F_phi d r c g)) 0 u v = (c * fderiv ℂ (fderiv ℂ g) 0 u v).re := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4) := Metric.mem_ball_self (by positivity)
  have hφ2 : ContDiff ℝ (2 : ℕ) (F_phi d r c g) := F_phi_contDiff hr hg c 2
  have hd : DifferentiableAt ℝ (fderiv ℝ (F_phi d r c g)) 0 :=
    ((hφ2.fderiv_right (m := 1) (by norm_num)).differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun y => fderiv ℝ (F_phi d r c g) y v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ (F_phi d r c g)) 0)) 0 :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp 0 hd.hasFDerivAt
  have h2 : HasFDerivAt (fun y => realPartMulCLM c (fderiv ℂ g y v))
      ((realPartMulCLM c).comp (((ContinuousLinearMap.apply ℂ ℂ v).comp (fderiv ℂ (fderiv ℂ g) 0)).restrictScalars ℝ)) 0 :=
    (realPartMulCLM c).hasFDerivAt.comp 0 ((F_hasFDerivAt_apply hr hg v).restrictScalars ℝ)
  have hev : (fun y => fderiv ℝ (F_phi d r c g) y v) =ᶠ[𝓝 0] fun y => realPartMulCLM c (fderiv ℂ g y v) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds h0] with y hy
    rw [F_phi_fderiv hr hg c hy, F_T_apply]
  have h3 := (h2.congr_of_eventuallyEq hev).unique h1
  have h4 := congrArg (fun L => L u) h3
  exact h4.symm
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
