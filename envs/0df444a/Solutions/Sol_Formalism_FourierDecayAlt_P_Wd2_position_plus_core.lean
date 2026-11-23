-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.position_plus_core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:00.604115+00:00
-- url     : https://prove2.me/submissions/7deabac1-bf6d-4508-b5a3-bb19b74bf1ae

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
theorem _root_.solution (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (D : K) (hM : FreeOf2 a M) (hN : FreeOf2 a N)
    (H : ∀ i j k l, D • (M i j * N k l) - M k j * N i l = D • (N k l * M i j) - N k j * M i l) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) =
      d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by
  have hins : ∀ (c : S) (X : M2 (SlopeTestRemainingChoices S A)), ins c X = ∑ k, ∑ l, eU c k l * X k l :=
    fun _ _ => rfl
  have hdm : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (d0 c * X) i j = c * X i j :=
    fun c X i j => by simp [d0, Matrix.diagonal_mul]
  have hmd : ∀ (c : SlopeTestRemainingChoices S A) (X : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2), (X * d0 c) i j = X i j * c :=
    fun c X i j => by simp [d0, Matrix.mul_diagonal]
  have hR : ∀ x : SlopeTestRemainingChoices S A, ins a N * x = ins a (Matrix.of fun k l => N k l * x) := by
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
  rw [Matrix.mul_apply (M := P0 a) (N := M), Matrix.mul_apply (M := d0 (ins a N) * M) (N := P0 a)]
  simp only [hdm, P0, Matrix.of_apply, Finset.sum_mul]
  have e1 : ∀ p, eU a p i * M p j * ins a N = ∑ l, eU a p l * (M p j * N i l) := by
    intro p
    rw [mul_assoc, free_mul_ins a (M p j) (hM p j) N, eU_mul_ins]
    simp only [Matrix.of_apply]
  have e2 : ∀ p, ins a N * M i p * eU a j p = ∑ k, eU a k p * (N k j * M i p) := by
    intro p
    have hF : FreeOf2 a (Matrix.of fun k l => N k l * M i p) := fun k l c d => by
      simp only [Matrix.of_apply]
      exact (hN k l c d).mul_right (hM i p c d)
    rw [hR (M i p), ins_mul_eU a _ hF]
    simp only [Matrix.of_apply]
  have e3 : ∑ p, ∑ k, eU a k p * (N k j * M i p) = ∑ k, ∑ l, eU a k l * (N k j * M i l) :=
    Finset.sum_comm
  simp only [e1, e2]
  rw [e3]
  have hX : M i j * ins a N = ∑ k, ∑ l, eU a k l * (M i j * N k l) :=
    (free_mul_ins a (M i j) (hM i j) N).trans rfl
  have hY : ins a N * M i j = ∑ k, ∑ l, eU a k l * (N k l * M i j) := (hR (M i j)).trans rfl
  have key : ∀ f g : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A, D • (∑ k, ∑ l, eU a k l * f k l) -
      ∑ k, ∑ l, eU a k l * g k l = ∑ k, ∑ l, eU a k l * (D • f k l - g k l) := by
    intro f g
    simp only [Finset.smul_sum, ← mul_smul_comm, ← Finset.sum_sub_distrib, mul_sub]
  rw [hX, hY]
  refine (key (fun k l => M i j * N k l) (fun k l => M k j * N i l)).trans
    (Eq.trans ?_ (key (fun k l => N k l * M i j) (fun k l => N k j * M i l)).symm)
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (eU a k l * ·) (H i j k l)
end Formalism.FourierDecayAlt.P.Wd2
