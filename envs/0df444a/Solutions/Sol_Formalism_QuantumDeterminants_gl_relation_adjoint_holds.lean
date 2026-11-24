-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gl_relation_adjoint_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:52:08.571112+00:00
-- url     : https://prove2.me/submissions/a5b53b8a-8f49-4914-87e8-95540abbe443

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.REAL
noncomputable section
namespace Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private lemma commutator_sum_smul_eq_sum_sum_smul_commutator {A : Type*} [Ring A] [Algebra ℂ A] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (r : ι → ℂ) (x : ι → A) (s : κ → ℂ) (y : κ → A) :
    (∑ i, r i • x i) * (∑ k, s k • y k) - (∑ k, s k • y k) * (∑ i, r i • x i) =
      ∑ i, ∑ k, (r i * s k) • (x i * y k - y k * x i) := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, smul_sub, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by congr 1; ring
private lemma commutator_right_transform_of_commutation_relation {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (M Q : Matrix (Fin n) (Fin n) ℂ)
    (hE : ∀ a b c d, E a b * E c d - E c d * E a b = M b c • E a d - M d a • E c b)
    (a b c d : Fin n) :
    (∑ j, Q b j • E a j) * (∑ l, Q d l • E c l) - (∑ l, Q d l • E c l) * (∑ j, Q b j • E a j) =
      (Q * M) b c • (∑ l, Q d l • E a l) - (Q * M) d a • (∑ j, Q b j • E c j) := by
  rw [commutator_sum_smul_eq_sum_sum_smul_commutator]
  simp only [hE, smul_sub, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
    smul_smul, Finset.sum_mul]
  congr 1
  · first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
    | (rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
  · first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
    | (rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
private lemma commutator_left_transform_of_commutation_relation {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (F : Fin n → Fin n → A)
    (M P : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ a b c d, F a b * F c d - F c d * F a b = M b c • F a d - M d a • F c b)
    (a b c d : Fin n) :
    (∑ i, P i a • F i b) * (∑ k, P k c • F k d) - (∑ k, P k c • F k d) * (∑ i, P i a • F i b) =
      (M * P) b c • (∑ i, P i a • F i d) - (M * P) d a • (∑ k, P k c • F k b) := by
  rw [commutator_sum_smul_eq_sum_sum_smul_commutator]
  simp only [hF, smul_sub, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum,
    smul_smul, Finset.sum_mul]
  congr 1
  · first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
    | (rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
  · first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
    | (rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
       congr 1 <;> ring)
end Formalism.QuantumDeterminants
end
end

set_option autoImplicit false
open Matrix Formalism.REAL
noncomputable section
open Formalism Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution : GlRelAd := by
  intro A _ _ n E P Q hE hQP
  have h1 : ∀ a b c d, E a b * E c d - E c d * E a b =
      (1 : Matrix (Fin n) (Fin n) ℂ) b c • E a d - (1 : Matrix (Fin n) (Fin n) ℂ) d a • E c b := by
    intro a b c d
    rw [hE a b c d]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul]
  have h3 := commutator_left_transform_of_commutation_relation (fun a b => ∑ j, Q b j • E a j) (Q * 1) P (commutator_right_transform_of_commutation_relation E 1 Q h1)
  beta_reduce at h3
  have e : ∀ a b, (∑ c, ∑ d, (P c a * Q b d) • E c d) = ∑ i, P i a • ∑ j, Q b j • E i j := by
    intro a b
    simp only [Finset.smul_sum, smul_smul]
  intro a b c d
  simp only [e]
  rw [h3 a b c d, Matrix.mul_one, hQP]
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul]
end Formalism.QuantumDeterminants
