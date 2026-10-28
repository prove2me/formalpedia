-- Prove2me | solution 1 for CostlySeeding.EdgeQuery.submodular
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:36:22.943759+00:00
-- url     : https://prove2.me/submissions/6f8f7562-636c-420a-824e-7466611c8346

import Definitions.Def_CostlySeeding_EdgeQuery_Algorithm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators
open Finset CostlySeeding.EdgeQuery

private lemma Y_mono {n : ℕ} (E : Finset (Sym2 (Fin n))) (v : Fin n)
    (S U : Finset (Fin n)) (hSU : S ⊆ U) : Y E v S ≤ Y E v U := by
  classical
  unfold Y
  split_ifs with hS hU hU
  · exact le_rfl
  · obtain ⟨s, hs, hr⟩ := hS
    exact False.elim (hU ⟨s, hSU hs, hr⟩)
  · norm_num
  · exact le_rfl

private lemma Y_submod {n : ℕ} (E : Finset (Sym2 (Fin n))) (v : Fin n)
    (S U : Finset (Fin n)) : Y E v (S ∪ U) + Y E v (S ∩ U) ≤ Y E v S + Y E v U := by
  classical
  let R := fun s => (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).Reachable v s
  have hU : (∃ s ∈ S ∪ U, R s) ↔ (∃ s ∈ S, R s) ∨ (∃ s ∈ U, R s) := by
    constructor
    · rintro ⟨s, hs, hr⟩
      rcases mem_union.mp hs with hs|hs
      · exact Or.inl ⟨s, hs, hr⟩
      · exact Or.inr ⟨s, hs, hr⟩
    · rintro (⟨s,hs,hr⟩|⟨s,hs,hr⟩)
      · exact ⟨s, mem_union_left _ hs, hr⟩
      · exact ⟨s, mem_union_right _ hs, hr⟩
  have hI : (∃ s ∈ S ∩ U, R s) → (∃ s ∈ S, R s) ∧ (∃ s ∈ U, R s) := by
    rintro ⟨s, hs, hr⟩
    exact ⟨⟨s, (mem_inter.mp hs).1, hr⟩, ⟨s, (mem_inter.mp hs).2, hr⟩⟩
  change (if ∃ s ∈ S ∪ U, R s then 1 else 0) + (if ∃ s ∈ S ∩ U, R s then 1 else 0) ≤
    (if ∃ s ∈ S, R s then 1 else 0) + (if ∃ s ∈ U, R s then 1 else 0)
  by_cases hs : ∃ s ∈ S, R s <;> by_cases hu : ∃ s ∈ U, R s <;>
    by_cases hi : ∃ s ∈ S ∩ U, R s
  all_goals simp_all only [hU, true_or, or_true, false_or, or_false, if_true, if_false]
  all_goals norm_num

theorem solution (n T tau : ℕ) (hT : 0 < T) (htau : 0 < tau)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Vrho : Finset (Fin n)) (rho : ℝ) (hrho : 0 < rho)
    (ss : Fin T → ProbeSeed n) :
    MonotoneSet (GamCut G Vrho rho tau ss) ∧
      SubmodularSet (GamCut G Vrho rho tau ss) := by
  constructor
  · intro S U hSU
    unfold GamCut
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro v hv
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sum_le_sum fun i _ => Y_mono _ _ S U hSU
  · intro S U
    have hsum :
        (∑ v ∈ Vrho, (1 / (T : ℝ)) * ∑ i : Fin T, Y (probeCopy G Vrho tau (ss i)).1 v (S ∪ U)) +
        (∑ v ∈ Vrho, (1 / (T : ℝ)) * ∑ i : Fin T, Y (probeCopy G Vrho tau (ss i)).1 v (S ∩ U)) ≤
        (∑ v ∈ Vrho, (1 / (T : ℝ)) * ∑ i : Fin T, Y (probeCopy G Vrho tau (ss i)).1 v S) +
        (∑ v ∈ Vrho, (1 / (T : ℝ)) * ∑ i : Fin T, Y (probeCopy G Vrho tau (ss i)).1 v U) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_le_sum
      intro v hv
      rw [← mul_add, ← mul_add, ← sum_add_distrib, ← sum_add_distrib]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum fun i _ => Y_submod _ _ S U
    simpa only [GamCut, mul_add] using mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 1 / rho)

#print axioms solution
