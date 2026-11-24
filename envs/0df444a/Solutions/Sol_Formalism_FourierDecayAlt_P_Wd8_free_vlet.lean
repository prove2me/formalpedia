-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.free_vlet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:18.864532+00:00
-- url     : https://prove2.me/submissions/d10f32b9-ea35-43ef-a76d-20ad31c3be98

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_comm_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_eU_comm_of_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_comm_of_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_comm_of_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_comm_eU


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd8
theorem _root_.solution (σ : Site A) (l : Letter K S) {a : S} (ha : a ≠ l.intersection_update_fsHerm_neg_one) (i j : Fin 2) :
    Commute (eU a i j : SlopeTestRemainingChoices S A) (vlet σ l) := by
  unfold vlet ins
  refine Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun m _ => ?_
  exact (eU_comm_of_ne ha i j k m).mul_right
    (io_comm_eU ((if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) k m) a i j).symm
end Formalism.FourierDecayAlt.P.Wd8
