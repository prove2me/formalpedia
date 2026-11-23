-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.lift_reduction_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:40.459568+00:00
-- url     : https://prove2.me/submissions/c41003dc-8c40-4c16-a5dd-db8755e67421

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_mul


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
theorem _root_.solution (M N : M2 A) : (lift0 (M * N) : M2 (SlopeTestRemainingChoices S A)) = lift0 M * lift0 N := by
  refine Matrix.ext fun i j => ?_
  simp only [lift0, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two, io_add, io_mul]
end Formalism.FourierDecayAlt.P.Wd8
