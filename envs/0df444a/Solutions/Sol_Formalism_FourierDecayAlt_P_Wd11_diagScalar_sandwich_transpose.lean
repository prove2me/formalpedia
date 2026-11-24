-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.diagScalar_sandwich_transpose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:13:44.173608+00:00
-- url     : https://prove2.me/submissions/8414db3a-d4e9-4bf9-826c-9fcb07ed9720

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_mul_diagScalar_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (x y : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) :
    (d0 x * M * d0 y)ᵀ = d0 x * Mᵀ * d0 y := by
  ext1 i j
  rw [Matrix.transpose_apply, mul_diagScalar_apply, diagScalar_mul_apply, mul_diagScalar_apply, diagScalar_mul_apply,
    Matrix.transpose_apply]
end Formalism.FourierDecayAlt.P.Wd11
