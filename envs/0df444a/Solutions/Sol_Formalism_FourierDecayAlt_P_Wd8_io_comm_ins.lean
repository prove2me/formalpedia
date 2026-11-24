-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.io_comm_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:58.491105+00:00
-- url     : https://prove2.me/submissions/3585eae7-6835-4377-9853-fb377412ed68

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_comm_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_comm_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_comm_eU
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_comm_io


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
theorem _root_.solution (x : A) (a : S) (M : M2 A) (h : ∀ i j, Commute x (M i j)) :
    Commute (io x) (ins a (lift0 M) : SlopeTestRemainingChoices S A) := by
  unfold ins
  refine Commute.sum_right _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
  exact (io_comm_eU x a i j).mul_right (io_comm_io (h i j))
end Formalism.FourierDecayAlt.P.Wd8
