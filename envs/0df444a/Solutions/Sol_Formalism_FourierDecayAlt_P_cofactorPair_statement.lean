-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.cofactorPair_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:40:35.902526+00:00
-- url     : https://prove2.me/submissions/e17e1c13-2e9c-4969-8158-27781ca5afc1

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
theorem _root_.solution : C7.CofactorPair := by
  intro V _ _ B r f x'
  constructor
  · intro a
    have h := congrArg (fun M => M a (Fin.last r)) (Matrix.mul_adjugate (C7.zhat B f x'))
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h
    unfold C7.cofX'
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [← h]
    apply Finset.sum_congr rfl; intro b _; rw [mul_comm]; rfl
  · intro b
    have h := congrArg (fun M => M (Fin.last r) b) (Matrix.adjugate_mul (C7.zhat B f x'))
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero] at h
    unfold C7.cofX
    simp only [map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, Complex.conj_conj]
    have e : (if b = Fin.last r then (C7.zhat B f x').det else 0) =
        (if Fin.last r = b then (C7.zhat B f x').det else 0) := by
      by_cases hb : b = Fin.last r <;> simp [hb, eq_comm]
    rw [e, ← h]
    rfl
end Formalism.FourierDecayAlt.P
