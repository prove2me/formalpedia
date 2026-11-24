-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.liftMatrix_list_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:38.800163+00:00
-- url     : https://prove2.me/submissions/9079e0b0-12cb-4f6a-8dd0-bfe6e740f356

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_lift_reduction_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_liftMatrix_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_lift_reduction_mul


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
theorem _root_.solution (L : List (M2 A)) :
    (lift0 L.prod : M2 (SlopeTestRemainingChoices S A)) = (L.map lift0).prod := by
  induction L with
  | nil => simp [liftMatrix_one]
  | cons M L ih => simp [lift_reduction_mul, ih]
end Formalism.FourierDecayAlt.P.Wd8
