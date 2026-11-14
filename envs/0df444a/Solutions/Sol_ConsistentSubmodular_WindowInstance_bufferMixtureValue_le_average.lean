-- Prove2me | solution 1 for ConsistentSubmodular.WindowInstance.bufferMixtureValue_le_average
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:29:28.833817+00:00
-- url     : https://prove2.me/submissions/01984246-3a1f-455a-9348-7d55f68aedbe

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation
import Theorems.Thm_ConsistentSubmodular_finiteExpectation_mem
import Theorems.Thm_ConsistentSubmodular_Objective_value_biUnion_le

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem finiteExpectation_add (p : ι → ℝ) (v w : Finset ι → ℝ) :
    finiteExpectation p (fun S => v S + w S) = finiteExpectation p v + finiteExpectation p w := by
  simp only [finiteExpectation, mul_add, Finset.sum_add_distrib]

theorem finiteExpectation_mul (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) :
    finiteExpectation p (fun S => c * v S) = c * finiteExpectation p v := by
  simp only [finiteExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem finiteExpectation_sum {β : Type*} [Fintype β] (p : ι → ℝ)
    (v : β → Finset ι → ℝ) :
    finiteExpectation p (fun S => ∑ a, v a S) = ∑ a, finiteExpectation p (v a) := by
  simp only [finiteExpectation, Finset.mul_sum]
  exact Finset.sum_comm

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem solution (Q : Finset (Fin n)) {p : Point W.lastStage}
    (hp : IsSimplex p) :
    W.bufferMixtureValue Q p ≤ ∑ i, p i * W.objective.value (Q ∪ W.candidate i) := by
  have hcube : ∀ i, 0 ≤ p i ∧ p i ≤ 1 := fun i =>
    ⟨hp.1 i, hp.2 ▸ Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)⟩
  let d : Fin (W.lastStage + 1) → ℝ := fun i =>
    W.objective.value (Q ∪ W.candidate i) - W.objective.value Q
  have hpoint : ∀ I : Finset (Fin (W.lastStage + 1)),
      W.objective.value (Q ∪ I.biUnion W.candidate) ≤
        W.objective.value Q + ∑ i, d i * (if i ∈ I then 1 else 0) := by
    intro I
    have h := W.objective.value_biUnion_le Q W.candidate I
    have hs : ∑ i ∈ I, d i = ∑ i, d i * (if i ∈ I then 1 else 0) := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [← hs]
    exact h
  have hmono := finiteExpectation_mono p hcube hpoint
  have hE : finiteExpectation p
      (fun I => W.objective.value Q + ∑ i, d i * (if i ∈ I then 1 else 0)) =
      W.objective.value Q + ∑ i, d i * p i := by
    simp only [finiteExpectation_add, finiteExpectation_const, finiteExpectation_sum,
      finiteExpectation_mul, finiteExpectation_mem]
  rw [hE] at hmono
  have hd : ∑ i, d i * p i =
      ∑ i, p i * W.objective.value (Q ∪ W.candidate i) - W.objective.value Q * ∑ i, p i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [d]; ring
  rw [hd, hp.2] at hmono
  exact hmono.trans_eq (by ring)

end
