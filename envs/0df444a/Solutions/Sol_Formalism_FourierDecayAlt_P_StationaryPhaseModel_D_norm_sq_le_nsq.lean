-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_norm_sq_le_nsq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:35.501566+00:00
-- url     : https://prove2.me/submissions/248cff07-fafe-4975-a1fa-1ea752c598ff

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel

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
theorem _root_.solution (d : ℕ) (x : Fin d → ℂ) : ‖x‖ ^ 2 ≤ D_nsq d x := by
  have h0 : 0 ≤ D_nsq d x := by unfold D_nsq; positivity
  have h1 : ‖x‖ ≤ Real.sqrt (D_nsq d x) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro k
    apply Real.le_sqrt_of_sq_le
    unfold D_nsq
    exact Finset.single_le_sum (f := fun k => ‖x k‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ k)
  calc ‖x‖ ^ 2 ≤ Real.sqrt (D_nsq d x) ^ 2 := by gcongr
    _ = D_nsq d x := Real.sq_sqrt h0
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
