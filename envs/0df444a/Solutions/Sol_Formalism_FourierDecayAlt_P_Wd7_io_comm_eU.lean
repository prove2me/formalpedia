-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.io_comm_eU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:23.715994+00:00
-- url     : https://prove2.me/submissions/a569397b-c169-4873-b818-3769c2d12a13

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_mul_io_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_apply


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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (a : S) (i j : Fin 2) (x : A) : Commute (eU a i j : SlopeTestRemainingChoices S A) (io x) := by
  show (eU a i j : SlopeTestRemainingChoices S A) * io x = io x * eU a i j
  ext z y
  rw [io_mul_apply, mul_io_apply, eU_apply]
  split_ifs <;> simp
end Formalism.FourierDecayAlt.P.Wd7
