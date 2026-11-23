-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.sum_row_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:40.959318+00:00
-- url     : https://prove2.me/submissions/a6ea9deb-50d7-48e4-90d4-b234457f2f63

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_io_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_col_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_col_zero
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
theorem _root_.solution (U : SlopeTestRemainingChoices S A) (C : Fin 2 → SlopeTestRemainingChoices S A) (x : Fin 2 → A) (z : Ix S)
    (h : ∀ (k : Fin 2) (z' : Ix S), C k z' e1 = if k = 0 ∧ z' = e1 then 1 else 0) :
    (∑ k, U * C k * io (x k) : SlopeTestRemainingChoices S A) z e1 = U z e1 * x 0 := by
  rw [Matrix.sum_apply, Fin.sum_univ_two, mul_io_apply, mul_io_apply,
    mul_col_fix U (C 0) z (fun z' => by simp [h]), mul_col_zero U (C 1) z (fun z' => by simp [h])]
  simp
end Formalism.FourierDecayAlt.P.Wd8
