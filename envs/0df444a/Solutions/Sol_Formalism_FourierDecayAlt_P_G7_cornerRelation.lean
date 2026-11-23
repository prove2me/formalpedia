-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G7.cornerRelation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:23.423636+00:00
-- url     : https://prove2.me/submissions/7d0cc58b-d17b-4646-b7c3-a0fab2ab395d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_strictUpper_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_isStrictUpper_strictUpper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G7_pow_card_strict

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G7
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G2
namespace Formalism.FourierDecayAlt.P.G7
theorem _root_.solution : CornerRelation := by
  intro n t c a b v
  have hXs : IsStrictUpper (Xof t v) := by
    rw [Xof, ← strictUpper_smul]; exact isStrictUpper_strictUpper _
  set X := Xof t v with hX
  set B := t • b with hB
  set S : Matrix (Fin n) (Fin n) ℂ :=
    ∑ j ∈ Finset.range n, (-X) ^ j * (t • (1 : Matrix (Fin n) (Fin n) ℂ)) ^ (n - 1 - j) with hS
  have hgeom : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * S = t ^ n • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have hc : Commute (-X) (t • (1 : Matrix (Fin n) (Fin n) ℂ)) := (Commute.one_right _).smul_right t
    have h1 := hc.mul_geom_sum₂ n
    rw [neg_pow, pow_card_strict X hXs, mul_zero, zero_sub, smul_pow, one_pow] at h1
    have h2 : (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X) * S =
        -((-X - t • (1 : Matrix (Fin n) (Fin n) ℂ)) * S) := by
      rw [← neg_mul]; congr 1; abel
    rw [h2, h1, neg_neg]
  have hρ : rhoOf t a v = a ᵥ* (wMat n * (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X)) := by
    simp only [rhoOf, hX, Xof, G.upper]
    rw [← Matrix.vecMul_smul, ← Matrix.mul_smul, smul_add]
  have hsum : ∑ j ∈ Finset.range n, (rhoOf t a v ⬝ᵥ ((-X) ^ j *ᵥ B)) * t ^ (n - 1 - j) =
      rhoOf t a v ⬝ᵥ (S *ᵥ B) := by
    rw [hS, Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_pow, one_pow, Matrix.mul_smul, mul_one, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      mul_comm]
  have hfin : (a ᵥ* (wMat n * (t • (1 : Matrix (Fin n) (Fin n) ℂ) + X))) ⬝ᵥ (S *ᵥ B) =
      t ^ n * (a ⬝ᵥ (wMat n *ᵥ B)) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, mul_assoc, hgeom, Matrix.mul_smul, mul_one,
      Matrix.vecMul_smul, smul_dotProduct, ← Matrix.dotProduct_mulVec, smul_eq_mul]
  rw [hsum, hρ, hfin]
  ring
end Formalism.FourierDecayAlt.P.G7
