-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cofactor_corner_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:45:19.164358+00:00
-- url     : https://prove2.me/submissions/b9630c69-52a9-4a80-af64-3fbad138ecd2

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmegaNormCofactorOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.CofactorCorner := by
  intro r Z
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  unfold C7.minorR
  have : ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]; simp
  rw [this, one_mul]
end Formalism.FourierDecayAlt.P
