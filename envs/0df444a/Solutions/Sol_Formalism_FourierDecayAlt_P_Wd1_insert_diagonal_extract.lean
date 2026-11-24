-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd1.insert_diagonal_extract
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:08.398928+00:00
-- url     : https://prove2.me/submissions/e490fbe6-751c-43a6-8644-154a30c6bb00

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_sum_eU_diag

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
theorem _root_.solution (a : S) (b : SlopeTestRemainingChoices S A) : ins a (d0 b) = b := by
  simp only [ins, d0, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [← Finset.sum_mul, sum_eU_diag, one_mul]
end Formalism.FourierDecayAlt.P.Wd1
