-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd1.ins_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:58.069802+00:00
-- url     : https://prove2.me/submissions/22046e2a-8cf5-4394-93b3-2fe15af8dfb2

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_eU_comm_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd1
open Matrix Formalism.FourierDecayAlt.Wd
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd1
theorem _root_.solution {a c : S} (hc : c ≠ a) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 c M) :
    FreeOf c (ins a M) := by
  intro k l
  unfold ins
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact (eU_comm_of_ne hc k l i j).mul_right (hM i j k l)
end Formalism.FourierDecayAlt.P.Wd1
