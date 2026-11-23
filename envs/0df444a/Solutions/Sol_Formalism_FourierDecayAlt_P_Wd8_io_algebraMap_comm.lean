-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.io_algebraMap_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:14.865801+00:00
-- url     : https://prove2.me/submissions/883d8a3b-d645-47b3-9a93-ab246ebc4cee

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_io_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_io_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_io_apply


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
theorem _root_.solution (k : K) (b : SlopeTestRemainingChoices S A) : Commute (io (algebraMap K A k)) b := by
  show (io (algebraMap K A k) : SlopeTestRemainingChoices S A) * b = b * io (algebraMap K A k)
  refine Matrix.ext fun z z' => ?_
  rw [io_mul_apply, mul_io_apply]
  exact Algebra.commutes k (b z z')
end Formalism.FourierDecayAlt.P.Wd8
