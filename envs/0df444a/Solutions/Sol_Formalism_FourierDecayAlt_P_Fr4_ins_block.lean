-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.ins_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:08.427792+00:00
-- url     : https://prove2.me/submissions/5bdde773-285b-4363-8c80-68c9fdf82ad0

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_sum_eU_diag


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr4
variable {A S : Type} [Ring A] [Algebra ℂ A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr4
theorem _root_.solution (a : S) (c D : ℂ) (x : SlopeTestRemainingChoices S A) (y : Fin 2 → SlopeTestRemainingChoices S A) (m : Fin 2) :
    ins a (Matrix.of fun k l => c • (D • (if k = l then x else 0) - (if k = m then y l else 0))) =
      c • (D • x - (eU a m 0 * y 0 + eU a m 1 * y 1)) := by
  have h1 := Wd1.sum_eU_diag (A := A) a
  rw [Fin.sum_univ_two] at h1
  have h2 : x = eU a 0 0 * x + eU a 1 1 * x := by rw [← add_mul, h1, one_mul]
  unfold ins
  conv_rhs => rw [h2]
  fin_cases m <;>
    simp [Fin.sum_univ_two, mul_sub, smul_sub, smul_add]
end Formalism.FourierDecayAlt.P.Fr4
