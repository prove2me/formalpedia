-- Prove2me | solution 1 for Expanders.quadForm_eq_of_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:40:25.126768+00:00
-- url     : https://prove2.me/submissions/599b6a84-4cfd-4472-8f58-c7102a0ab5d6

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
public import Theorems.Thm_Expanders_dotProduct_adjMatrix_mulVec
public import Theorems.Thm_Expanders_sum_neighbor_swap

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (f : V → ℝ) (c : V → V → ℝ)
    (hc : ∀ v, ∀ w ∈ G.neighborFinset v, (f v - f w) ^ 2 = c v w + c w v) :
    dotProduct f (G.adjMatrix ℝ *ᵥ f) =
      d * ∑ v, f v ^ 2 - ∑ v, ∑ w ∈ G.neighborFinset v, c v w := by
  rw [dotProduct_adjMatrix_mulVec, Finset.mul_sum]
  have e1 : ∀ v, f v * ∑ w ∈ G.neighborFinset v, f w =
      ∑ w ∈ G.neighborFinset v, ((f v ^ 2 + f w ^ 2) - (c v w + c w v)) / 2 := by
    intro v
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [← hc v w hw]; ring
  simp_rw [e1]
  have hP : ∀ v, ∑ w ∈ G.neighborFinset v, f v ^ 2 = d * f v ^ 2 := by
    intro v
    rw [Finset.sum_const, card_neighborFinset_eq_degree, hd v, nsmul_eq_mul]
  have hQ := sum_neighbor_swap G (fun v w => f v ^ 2)
  have hC := sum_neighbor_swap G (fun v w => c v w)
  have split : ∀ v, ∑ w ∈ G.neighborFinset v, ((f v ^ 2 + f w ^ 2) - (c v w + c w v)) / 2 =
      (∑ w ∈ G.neighborFinset v, f v ^ 2 + ∑ w ∈ G.neighborFinset v, f w ^ 2
        - ∑ w ∈ G.neighborFinset v, c v w - ∑ w ∈ G.neighborFinset v, c w v) / 2 := by
    intro v
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl (fun w _ => ?_); ring
  simp_rw [split, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← hQ, ← hC]
  simp only [hP]
  ring
end Expanders
