-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr4.blk_plus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:58:43.735868+00:00
-- url     : https://prove2.me/submissions/5fb3b02a-937b-4ede-a24b-2aa7058bd599

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FreeOf2RmatrixTranspose

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
theorem _root_.solution (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ) (i j k l : Fin 2) :
    Formalism.YangianSpanCharacter.F.blk (E1 M *
      ((D - 1)⁻¹ • (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)))) i j k l =
      (D - 1)⁻¹ • (D • (if k = l then M i j else 0) - (if k = j then M i l else 0)) := by
  unfold Formalism.YangianSpanCharacter.F.blk E1 Pf
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, mul_sub]
end Formalism.FourierDecayAlt.P.Fr4
