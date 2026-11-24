-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.io_comm_eU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:32.442979+00:00
-- url     : https://prove2.me/submissions/d28142e1-76e1-4262-ab5e-7238dcf8b0f7

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
theorem _root_.solution (x : A) (a : S) (i j : Fin 2) : Commute (io x) (eU a i j : SlopeTestRemainingChoices S A) := by
  show (io x : SlopeTestRemainingChoices S A) * eU a i j = eU a i j * io x
  refine Matrix.ext fun z z' => ?_
  rw [io_mul_apply, mul_io_apply]
  simp only [eU, Matrix.of_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Wd8
