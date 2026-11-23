-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.position_minus_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:35.641365+00:00
-- url     : https://prove2.me/submissions/78fed6e9-38ad-47e5-a6db-247120496440

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_free_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_eU_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_ins_mul_eU

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd2
theorem _root_.solution (b : S) (M N : M2 (SlopeTestRemainingChoices S A)) (d : K) (hM : FreeOf2 b M) (hN : FreeOf2 b N)
    (H : ∀ i j k l, d • (N i j * M k l) - N k j * M i l = d • (M k l * N i j) - M k j * N i l) :
    d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M =
      M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) := by
  have hins : ∀ (c : S) (X : M2 (SlopeTestRemainingChoices S A)), ins c X = ∑ k, ∑ l, eU c k l * X k l :=
    fun _ _ => rfl
  have hdm : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (d0 c * X) i j = c * X i j :=
    fun c X i j => by simp [d0, Matrix.diagonal_mul]
  have hmd : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (X * d0 c) i j = X i j * c :=
    fun c X i j => by simp [d0, Matrix.mul_diagonal]
  have hNT : FreeOf2 b Nᵀ := fun k l => hN l k
  have hR : ∀ x : SlopeTestRemainingChoices S A, ins b Nᵀ * x = ins b (Matrix.of fun k l => Nᵀ k l * x) := by
    intro x
    unfold ins
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.of_apply, mul_assoc]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  ext i j : 1
  simp only [Matrix.sub_apply, Matrix.smul_apply, hmd, hdm]
  rw [Matrix.mul_apply (M := d0 (ins b Nᵀ) * Q0 b) (N := M), Matrix.mul_apply (M := M) (N := Q0 b)]
  simp only [hdm, Q0, Matrix.of_apply, Finset.sum_mul]
  have e1 : ∀ p, ins b Nᵀ * eU b i p * M p j = ∑ k, eU b k p * (N i k * M p j) := by
    intro p
    rw [ins_mul_eU b _ hNT, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Matrix.transpose_apply]
  have e2 : ∀ p, M i p * eU b p j * ins b Nᵀ = ∑ l, eU b p l * (M i p * N l j) := by
    intro p
    rw [← (hM i p p j).eq, mul_assoc, free_mul_ins b (M i p) (hM i p) Nᵀ, eU_mul_ins]
    simp only [Matrix.of_apply, Matrix.transpose_apply]
  have e3 : ∑ p, ∑ k, eU b k p * (N i k * M p j) = ∑ k, ∑ l, eU b k l * (N i k * M l j) :=
    Finset.sum_comm
  simp only [e1, e2]
  rw [e3]
  have hX : ins b Nᵀ * M i j = ∑ k, ∑ l, eU b k l * (N l k * M i j) := (hR (M i j)).trans rfl
  have hY : M i j * ins b Nᵀ = ∑ k, ∑ l, eU b k l * (M i j * N l k) :=
    (free_mul_ins b (M i j) (hM i j) Nᵀ).trans rfl
  have key : ∀ f g : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A, d • (∑ k, ∑ l, eU b k l * f k l) -
      ∑ k, ∑ l, eU b k l * g k l = ∑ k, ∑ l, eU b k l * (d • f k l - g k l) := by
    intro f g
    simp only [Finset.smul_sum, ← mul_smul_comm, ← Finset.sum_sub_distrib, mul_sub]
  rw [hX, hY]
  refine (key (fun k l => N l k * M i j) (fun k l => N i k * M l j)).trans
    (Eq.trans ?_ (key (fun k l => M i j * N l k) (fun k l => M i k * N l j)).symm)
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (eU b k l * ·) (H l k i j)
end Formalism.FourierDecayAlt.P.Wd2
