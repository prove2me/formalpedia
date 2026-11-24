-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.l_mat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:22:37.355467+00:00
-- url     : https://prove2.me/submissions/5d2d26b8-9b05-4ac7-865e-e58ff592b68c

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution {B : Type*} [Ring B] {E Gb τn Ln N dg Ln' lm : Matrix (Fin 2) (Fin 2) B} (m3 : τn * Ln = N)
    (m4 : Gb * τn = dg * Gb) (m5 : Gb * Ln = Ln' * Gb) (e1 : E * dg = dg * E) (e2 : E * Ln' = lm * E) :
    E * Gb * N = dg * lm * (E * Gb) := by
  calc E * Gb * N = E * (Gb * τn) * Ln := by rw [← m3]; simp only [Matrix.mul_assoc]
    _ = E * dg * (Gb * Ln) := by rw [m4]; simp only [Matrix.mul_assoc]
    _ = dg * (E * Ln') * Gb := by rw [m5, e1]; simp only [Matrix.mul_assoc]
    _ = dg * lm * (E * Gb) := by rw [e2]; simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.Fr9
