-- Prove2me | solution 1 for BooleanMultilinear.off_cube_evaluation_requires_all_queries
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:46:35.304863+00:00
-- url     : https://prove2.me/submissions/cff87712-2c3f-4955-9f45-e7270b6d24a6

import Mathlib
open MvPolynomial
open scoped BigOperators

namespace BooleanQueryProof
open MvPolynomial
variable {F : Type*} [Field F] {r : ℕ}
noncomputable def addressBasis (address : Fin r → Bool) : MvPolynomial (Fin r) F :=
  ∏ i, if address i then X i else 1 - X i

/-- The multilinear extension of the Boolean residual. The finite sum
ranges over the failing addresses only. -/
noncomputable def extension (fails : (Fin r → Bool) → Bool) : MvPolynomial (Fin r) F :=
  ∑ a ∈ Finset.univ.filter (fun a => fails a = true), addressBasis a

theorem extension_zero_of_passes (fails : (Fin r → Bool) → Bool)
    (passes : ∀ a, fails a = false) : extension (F := F) fails = 0 := by
  classical
  simp [extension, passes]

theorem singleton_detected (a : Fin r → Bool) (z : Fin r → F)
    (away : ∀ i, z i ≠ 0 ∧ z i ≠ 1) :
    eval z (extension (fun b => decide (b = a))) ≠ 0 := by
  classical
  have support : (Finset.univ.filter
    (fun b : Fin r → Bool => decide (b = a) = true)) = {a} := by
    ext b
    simp
  unfold extension addressBasis
  rw [support, Finset.sum_singleton, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases h : a i
  · simp only [Bool.false_eq_true, if_false, map_sub, map_one, eval_X, sub_ne_zero]
    exact Ne.symm (away i).2
  · simpa [h] using (away i).1

end BooleanQueryProof

theorem solution {F : Type*} [Field F] {r : ℕ} (z : Fin r → F)
    (away : ∀ i, z i ≠ 0 ∧ z i ≠ 1)
    (queries : Finset (Fin r → Bool)) (few : queries.card < 2^r) :
    let extension (f : (Fin r → Bool) → Bool) : MvPolynomial (Fin r) F :=
      ∑ a ∈ Finset.univ.filter (fun a => f a = true), ∏ i, (if a i then X i else 1 - X i)
    ∃ f g : (Fin r → Bool) → Bool,
      (∀ a ∈ queries, f a = g a) ∧ eval z (extension f) ≠ eval z (extension g) := by
  change ∃ f g : (Fin r → Bool) → Bool, (∀ a ∈ queries, f a = g a) ∧
    eval z (BooleanQueryProof.extension f) ≠ eval z (BooleanQueryProof.extension g)
  classical
  have missing : ∃ a : Fin r → Bool, a ∉ queries := by
    by_contra! total
    have full := Finset.eq_univ_of_forall total
    rw [full, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at few
    exact (Nat.lt_irrefl _) few
  obtain ⟨a,outside⟩ := missing
  refine ⟨fun _ => false, fun b => decide (b = a), ?_, ?_⟩
  · intro b hb
    have different : b ≠ a := fun eq => outside (eq ▸ hb)
    simp [different]
  · rw [BooleanQueryProof.extension_zero_of_passes _ (fun _ => rfl), map_zero]
    exact Ne.symm (BooleanQueryProof.singleton_detected a z away)
