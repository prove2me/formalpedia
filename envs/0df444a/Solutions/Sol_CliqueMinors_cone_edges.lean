-- Prove2me | solution 1 for CliqueMinors.cone_edges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:49.119621+00:00
-- url     : https://prove2.me/submissions/758f512a-a5d8-4213-a9fe-f03341454d70

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution {G : SimpleGraph V} {x : V} {m : ℕ}
    (hc : ∀ v, G.Adj x v → m ≤ (G.neighborFinset x ∩ G.neighborFinset v).card) :
    m * (G.neighborFinset x).card ≤ 2 * (coneG G x).edgeFinset.card := by
  rw [← sum_degrees_eq_twice_card_edges]
  calc m * (G.neighborFinset x).card = ∑ v ∈ G.neighborFinset x, m := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ v ∈ G.neighborFinset x, (coneG G x).degree v := by
        refine Finset.sum_le_sum fun v hv => ?_
        rw [mem_neighborFinset] at hv
        refine (hc v hv).trans ?_
        rw [← card_neighborFinset_eq_degree]
        refine Finset.card_le_card fun t ht => ?_
        simp only [Finset.mem_inter, mem_neighborFinset] at ht
        rw [mem_neighborFinset]
        exact ⟨ht.2, hv, ht.1⟩
    _ ≤ ∑ v, (coneG G x).degree v :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
end CliqueMinors
