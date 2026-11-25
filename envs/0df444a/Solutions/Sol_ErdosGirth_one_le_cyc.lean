-- Prove2me | solution 1 for ErdosGirth.one_le_cyc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:30:19.202528+00:00
-- url     : https://prove2.me/submissions/2d4613d8-19fa-4426-b5af-07140d6181e5

module
public import Mathlib
public import Definitions.Def_GirthLib_ErdosGirthAux

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosGirth
open Classical
namespace ErdosGirth
theorem _root_.solution {m g : ℕ} {S : Finset (Sym2 (Fin m))} {u : Fin m} (c : (gr S).Walk u u)
    (hc : c.IsCycle) (hl : c.length ≤ g) : 1 ≤ cyc m g S u := by
  have hE : ∀ e ∈ c.edges, e ∈ (S : Set (Sym2 (Fin m))) ∧ ¬ e.IsDiag := by
    intro e he
    have := c.edges_subset_edgeSet he
    rw [gr, edgeSet_fromEdgeSet] at this
    exact ⟨this.1, this.2⟩
  have hT : ∀ e ∈ c.edges, e ∈ (⊤ : SimpleGraph (Fin m)).edgeSet := by
    intro e he
    rw [edgeSet_top]
    exact (hE e he).2
  set c' := c.transfer ⊤ hT
  have hc' : c'.IsCycle := hc.transfer hT
  have hcond : c'.IsCycle ∧ c'.edges.toFinset ⊆ S := by
    refine ⟨hc', fun e he => ?_⟩
    rw [List.mem_toFinset, Walk.edges_transfer] at he
    exact (hE e he).1
  have hterm : (if c'.IsCycle ∧ c'.edges.toFinset ⊆ S then (1 : ℝ) else 0) = 1 := by
    simp only [hcond, and_self, ite_true]
  calc (1 : ℝ) = if c'.IsCycle ∧ c'.edges.toFinset ⊆ S then (1 : ℝ) else 0 := hterm.symm
    _ ≤ ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength c.length u u,
          if c.IsCycle ∧ c.edges.toFinset ⊆ S then (1 : ℝ) else 0 := by
        refine single_le_sum (f := fun c : (⊤ : SimpleGraph (Fin m)).Walk u u =>
          if c.IsCycle ∧ c.edges.toFinset ⊆ S then (1 : ℝ) else 0)
          (fun _ _ => by split_ifs <;> norm_num) ?_
        rw [mem_finsetWalkLength_iff, Walk.length_transfer]
    _ ≤ cyc m g S u := by
        refine single_le_sum (f := fun ℓ => ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
          if c.IsCycle ∧ c.edges.toFinset ⊆ S then (1 : ℝ) else 0)
          (fun _ _ => sum_nonneg fun _ _ => by split_ifs <;> norm_num) ?_
        rw [mem_range]; omega
end ErdosGirth
