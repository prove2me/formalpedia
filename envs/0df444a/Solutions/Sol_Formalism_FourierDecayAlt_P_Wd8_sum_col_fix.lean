-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd8.sum_col_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:40.455552+00:00
-- url     : https://prove2.me/submissions/43819607-8e42-4802-9bb7-4411950577b4

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_col_fix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_mul_col_zero

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
theorem _root_.solution (B C : Fin 2 → SlopeTestRemainingChoices S A) (z : Ix S)
    (h : ∀ (k : Fin 2) (z' : Ix S), C k z' e1 = if k = 0 ∧ z' = e1 then 1 else 0) :
    (∑ k, B k * C k) z e1 = B 0 z e1 := by
  rw [Matrix.sum_apply, Fin.sum_univ_two,
    mul_col_fix (B 0) (C 0) z (fun z' => by simp [h]),
    mul_col_zero (B 1) (C 1) z (fun z' => by simp [h]), add_zero]
end Formalism.FourierDecayAlt.P.Wd8
