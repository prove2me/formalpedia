-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.mul_rh0_apply_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:46.487796+00:00
-- url     : https://prove2.me/submissions/83f6c72f-7c1a-4dd7-a3cc-6c6069db96ff

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {a : S}
namespace Formalism.FourierDecayAlt.P.Fr7
theorem _root_.solution (M : M2 (SlopeTestRemainingChoices S A)) (D : ℂ) :
    (M * Rh0 a D : M2 (SlopeTestRemainingChoices S A)) 1 0 = (D - 1)⁻¹ • (D • M 1 0 - M 1 0 * eU a 0 0 - M 1 1 * eU a 0 1) := by
  simp only [Rh0, P0, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.one_apply, Matrix.of_apply]
  simp only [mul_smul_comm, mul_sub, smul_sub]
  simp
  module
end Formalism.FourierDecayAlt.P.Fr7
