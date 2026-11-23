-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd3.minus_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:01.294096+00:00
-- url     : https://prove2.me/submissions/2c76e5df-dbb7-4294-8ed7-45e51ba480dd

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_eU_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul_eU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd3
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd3
theorem _root_.solution (b : S) (M N : M2 (SlopeTestRemainingChoices S A)) (d : K) (hM : FreeOf2 b M) (hN : FreeOf2 b N)
    (h : ∀ i r j s, d • (N i j * M r s) - N r j * M i s = d • (M r s * N i j) - M r j * N i s) :
    d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M =
      M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) := by
  have hM' : ∀ i j, FreeOf b (M i j) := hM
  have hC : ∀ i j k l, Commute (eU b k l) (M i j) := fun i j => hM' i j
  have h1 : ∀ r s, FreeOf b (N r s) := hN
  have hT : FreeOf2 b Nᵀ := fun r s => h1 s r
  refine Matrix.ext fun i j => ?_
  have key : ∀ r s, d • (eU b r s * (N s r * M i j)) - eU b r s * (N i r * M s j) =
      d • (eU b r s * (M i j * N s r)) - eU b r s * (M i r * N s j) := fun r s => by
    have := congrArg (eU b r s * ·) (h s i r j)
    simp only [mul_sub, mul_smul_comm] at this
    exact this
  have hL : ((d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M : M2 (SlopeTestRemainingChoices S A))) i j =
      d • (ins b Nᵀ * M i j) - ∑ k, ins b Nᵀ * (M k j * eU b i k) := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.diagonal_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]
    exact congrArg (ins b Nᵀ * ·) (hC k j i k).eq
  have hR : ((M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) : M2 (SlopeTestRemainingChoices S A))) i j =
      d • (M i j * ins b Nᵀ) - ∑ k, eU b k j * M i k * ins b Nᵀ := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hC i k k j).eq]
    rfl
  rw [hL, hR, ins_mul, mul_ins b _ _ (hM' i j),
    Finset.sum_congr rfl fun k _ => ins_mul_eU b i k (M k j) Nᵀ (hM' k j) hT,
    Finset.sum_congr rfl fun k _ => eU_mul_ins b k j (M i k) Nᵀ (hM' i k),
    Finset.sum_comm (f := fun k r => eU b r k * (Nᵀ r i * M k j)),
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => key r s
end Formalism.FourierDecayAlt.P.Wd3
