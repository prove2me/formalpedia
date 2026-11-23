-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.det_abs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:52.531802+00:00
-- url     : https://prove2.me/submissions/355a7d1a-a43b-4f37-8a49-4f20c70036fa

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
variable {B : Type} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (τ0 τ1 i0 i1 i2 l0 l1 m0 m1 : B) (q0 q1 : ℂ)
    (h00 : τ0 * i0 = 1) (h00' : i0 * τ0 = 1) (h11 : τ1 * i1 = 1) (h11' : i1 * τ1 = 1)
    (hi : i0 * i1 = i1 * i0)
    (Y1 : l0 * τ1 = τ1 * l1) (Y1' : m1 * τ0 = τ0 * m0)
    (Y3 : m1 * l1 - l1 * m1 = q0 • (i0 * i1) - q1 • (i1 * i2)) :
    (q1 • i2 + τ1 * m1 * l1) * (τ0 * l0) - τ1 * l1 * (q0 • i1 + τ0 * m0 * l0) = 0 ∧
    (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) = algebraMap ℂ B q0 ∧
    τ1 * m1 * (τ0 * l0) - τ1 * (q0 • i1 + τ0 * m0 * l0) = -algebraMap ℂ B q0 ∧
    τ1 * m1 * τ0 - τ1 * (τ0 * m0) = 0 ∧
    (q0 • i1 + τ0 * m0 * l0) * (τ1 * m1) - τ0 * m0 * (q1 • i2 + τ1 * m1 * l1) = 0 ∧
    (q0 • i1 + τ0 * m0 * l0) * τ1 - τ0 * m0 * (τ1 * l1) = algebraMap ℂ B q0 ∧
    τ0 * l0 * (τ1 * m1) - τ0 * (q1 • i2 + τ1 * m1 * l1) = -algebraMap ℂ B q0 ∧
    τ0 * l0 * τ1 - τ0 * (τ1 * l1) = 0 := by
  have T5 : τ1 * (i0 * i1) = i0 := by rw [hi, ← mul_assoc, h11, one_mul]
  have FreeQuotientRank : τ1 * (i1 * i2) = i2 := by rw [← mul_assoc, h11, one_mul]
  have K : τ1 * (m1 * l1 - l1 * m1) = q0 • i0 - q1 • i2 := by
    rw [Y3, mul_sub, mul_smul_comm, mul_smul_comm, T5, FreeQuotientRank]
  have e2 : (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) = algebraMap ℂ B q0 := by
    have s : (q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0) =
        q1 • (i2 * τ0) + τ1 * (m1 * l1 - l1 * m1) * τ0 := by
      rw [← Y1']
      simp only [add_mul, smul_mul_assoc, mul_sub, sub_mul, mul_assoc]
      abel
    rw [s, K, sub_mul, smul_mul_assoc, smul_mul_assoc, h00', Algebra.algebraMap_eq_smul_one]
    abel
  have F1 : τ1 * l1 * i1 = l0 := by rw [← Y1, mul_assoc, h11, mul_one]
  have F2 : τ0 * m0 * i0 = m1 := by rw [← Y1', mul_assoc, h00, mul_one]
  refine ⟨?_, e2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have s : (q1 • i2 + τ1 * m1 * l1) * (τ0 * l0) - τ1 * l1 * (q0 • i1 + τ0 * m0 * l0) =
        ((q1 • i2 + τ1 * m1 * l1) * τ0 - τ1 * l1 * (τ0 * m0)) * l0 - q0 • (τ1 * l1 * i1) := by
      simp only [mul_add, add_mul, sub_mul, mul_smul_comm, smul_mul_assoc, mul_assoc]
      abel
    rw [s, e2, F1, ← Algebra.smul_def, sub_self]
  · have s : τ1 * m1 * (τ0 * l0) = τ1 * (τ0 * m0 * l0) := by
      rw [mul_assoc τ1, ← mul_assoc m1, Y1']
    rw [s, mul_add, mul_smul_comm, h11, Algebra.algebraMap_eq_smul_one]
    abel
  · rw [mul_assoc, Y1', sub_self]
  · have s : (q0 • i1 + τ0 * m0 * l0) * (τ1 * m1) - τ0 * m0 * (q1 • i2 + τ1 * m1 * l1) =
        q0 • (i1 * τ1 * m1) - τ0 * m0 * (τ1 * (m1 * l1 - l1 * m1)) - q1 • (τ0 * m0 * i2) := by
      have s2 : τ0 * m0 * l0 * (τ1 * m1) = τ0 * m0 * (τ1 * (l1 * m1)) := by
        rw [mul_assoc (τ0 * m0), ← mul_assoc l0, Y1, mul_assoc τ1]
      rw [add_mul, s2]
      simp only [mul_add, mul_sub, mul_smul_comm, smul_mul_assoc, mul_assoc]
      abel
    rw [s, K, h11', one_mul, mul_sub, mul_smul_comm, mul_smul_comm, F2]
    abel
  · rw [add_mul, smul_mul_assoc, h11', mul_assoc (τ0 * m0) l0 τ1, Y1, Algebra.algebraMap_eq_smul_one]
    abel
  · have s : τ0 * l0 * (τ1 * m1) - τ0 * (q1 • i2 + τ1 * m1 * l1) =
        -(τ0 * (τ1 * (m1 * l1 - l1 * m1))) - q1 • (τ0 * i2) := by
      have s2 : τ0 * l0 * (τ1 * m1) = τ0 * (τ1 * (l1 * m1)) := by
        rw [mul_assoc τ0, ← mul_assoc l0, Y1, mul_assoc]
      rw [s2]
      simp only [mul_add, mul_sub, mul_smul_comm, mul_assoc]
      abel
    rw [s, K, mul_sub, mul_smul_comm, mul_smul_comm, h00, Algebra.algebraMap_eq_smul_one]
    abel
  · rw [mul_assoc, Y1, sub_self]
end Formalism.FourierDecayAlt.P.Mx7
