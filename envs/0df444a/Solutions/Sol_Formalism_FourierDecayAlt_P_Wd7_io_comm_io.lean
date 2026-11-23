-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.io_comm_io
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:31.648729+00:00
-- url     : https://prove2.me/submissions/b24d13e6-9f2b-496d-a89c-930711f5d0a0

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_io_apply

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
theorem _root_.solution {x y : A} (h : Commute x y) : Commute (io x : SlopeTestRemainingChoices S A) (io y) := by
  show (io x : SlopeTestRemainingChoices S A) * io y = io y * io x
  ext z z'
  rw [io_mul_apply, io_mul_apply, io_apply, io_apply]
  split_ifs
  · exact h.eq
  · simp
end Formalism.FourierDecayAlt.P.Wd7
