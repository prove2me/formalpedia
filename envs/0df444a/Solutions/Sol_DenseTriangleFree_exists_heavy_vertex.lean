-- Prove2me | solution 1 for DenseTriangleFree.exists_heavy_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:47:20.43158+00:00
-- url     : https://prove2.me/submissions/62c59f49-4f12-478f-ae59-55a82699f5f9

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy

set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
namespace DenseTriangleFree
theorem _root_.solution (hδ : 10 * Fintype.card V < 29 * G.minDegree) {k : ℕ}
    (f : ℕ → V) (w : ℕ → ℕ) (hpos : 0 < ∑ i ∈ Finset.range k, w i) :
    ∃ y, 10 * ∑ i ∈ Finset.range k, w i <
      29 * ∑ i ∈ Finset.range k, (if G.Adj (f i) y then w i else 0) := by
  by_contra hno
  push Not at hno
  have key : (∑ i ∈ Finset.range k, w i) * (29 * G.minDegree) ≤
      (∑ i ∈ Finset.range k, w i) * (10 * Fintype.card V) := by
    calc (∑ i ∈ Finset.range k, w i) * (29 * G.minDegree)
        = 29 * ∑ i ∈ Finset.range k, w i * G.minDegree := by
          rw [Finset.sum_mul, Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ 29 * ∑ i ∈ Finset.range k, w i * G.degree (f i) := by
          gcongr with i
          exact G.minDegree_le_degree _
      _ = 29 * ∑ i ∈ Finset.range k, ∑ y, (if G.Adj (f i) y then w i else 0) := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter, Finset.card_filter,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          split_ifs <;> simp
      _ = ∑ y, 29 * ∑ i ∈ Finset.range k, (if G.Adj (f i) y then w i else 0) := by
          rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ ∑ _y : V, 10 * ∑ i ∈ Finset.range k, w i := Finset.sum_le_sum fun y _ => hno y
      _ = (∑ i ∈ Finset.range k, w i) * (10 * Fintype.card V) := by
          simp [Finset.card_univ]; ring
  have := le_of_mul_le_mul_left key hpos
  omega
end DenseTriangleFree
