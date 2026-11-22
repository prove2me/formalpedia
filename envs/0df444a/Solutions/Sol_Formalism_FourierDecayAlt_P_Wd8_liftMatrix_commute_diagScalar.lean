-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.liftMatrix_commute_diagScalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:17:56.220846+00:00
-- url     : https://prove2.me/submissions/bb3ac025-8d22-475d-9382-c3f3c59e1da9

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_diagScalar_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_diagScalar_mul_apply

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
theorem _root_.solution (M : M2 A) (b : SlopeTestRemainingChoices S A) (h : ∀ i j, Commute (io (M i j)) b) :
    Commute (lift0 M) (d0 b) := by
  show lift0 M * d0 b = d0 b * lift0 M
  refine Matrix.ext fun i j => ?_
  rw [mul_diagScalar_apply, diagScalar_mul_apply]
  exact (h i j).eq
end Formalism.FourierDecayAlt.P.Wd8
