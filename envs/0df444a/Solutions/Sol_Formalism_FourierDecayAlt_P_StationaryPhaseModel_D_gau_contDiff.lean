-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_gau_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:32.647564+00:00
-- url     : https://prove2.me/submissions/dbfd0c4f-42c4-456e-b197-bd860240717c

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_nsq_sym

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
theorem _root_.solution (d : ℕ) (δ : ℝ) (n : ℕ) : ContDiff ℝ n (D_gau d δ) := by
  obtain ⟨K, _, hS⟩ := D_nsq_sym d n
  have : D_gau d δ = fun x => Real.exp (-δ * D_nsq d x) := rfl
  rw [this]
  exact Real.contDiff_exp.comp (contDiff_const.mul hS.1)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
