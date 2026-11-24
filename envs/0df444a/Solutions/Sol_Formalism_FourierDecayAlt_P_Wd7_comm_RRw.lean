-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.comm_RRw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:32.24722+00:00
-- url     : https://prove2.me/submissions/1ac6995f-bc24-42de-85ba-336d3a197566

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_ins_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_io
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_comm_TTw
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_comm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (QQ : K → M2 A) (w : List (Letter K S)) (z : A)
    (hz : ∀ Y i j, Commute z (QQ Y i j)) : Commute (io z : SlopeTestRemainingChoices S A) (RRw QQ w) := by
  induction w with
  | nil => exact Commute.one_right _
  | cons l w ih =>
    simp only [RRw]
    refine ih.mul_right (ins_comm _ _ _ (free_io _ _) fun i j => ?_)
    split_ifs
    · exact comm_TTw QQ w z hz _ i j
    · exact comm_TTw QQ w z hz _ j i
end Formalism.FourierDecayAlt.P.Wd7
