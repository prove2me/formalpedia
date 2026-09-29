-- Prove2me | solution 1 for Conway99.srg_lambda_one_cliqueFree_four
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T11:15:03.441177+00:00
-- url     : https://prove2.me/submissions/2c7bc00a-f071-4102-b984-9a50276bfe9d

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Combinatorics.SimpleGraph.Clique

open Finset SimpleGraph

namespace Conway99CliqueAux

/-- In a strongly regular graph with `ℓ = 1`, adjacent vertices have exactly one common
neighbour, counted as a `Finset`. -/
lemma card_inter_neighborFinset_eq_one {V : Type} [Fintype V] [DecidableEq V]
    {g : SimpleGraph V} [DecidableRel g.Adj] {n k μ : ℕ} (h : g.IsSRGWith n k 1 μ)
    {x y : V} (hxy : g.Adj x y) :
    (g.neighborFinset x ∩ g.neighborFinset y).card = 1 := by
  have := h.of_adj x y hxy
  rw [← this, ← Set.toFinset_card]
  congr 1
  ext z
  simp [mem_commonNeighbors]

end Conway99CliqueAux

-- A strongly regular graph with lambda = 1 contains no 4-clique.
open Conway99CliqueAux in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (g : SimpleGraph V) [DecidableRel g.Adj] {n k μ : ℕ} (h : g.IsSRGWith n k 1 μ) :
    g.CliqueFree 4 := by
  intro s hs
  obtain ⟨hclique, hcard⟩ := hs
  have h1 : 0 < s.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.1 h1
  have h2 : 0 < (s.erase a).card := by
    rw [Finset.card_erase_of_mem ha, hcard]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 h2
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  have hbs : b ∈ s := Finset.mem_of_mem_erase hb
  have hab : g.Adj a b := hclique ha hbs (Ne.symm hba)
  have hsub : (s.erase a).erase b ⊆ g.neighborFinset a ∩ g.neighborFinset b := by
    intro c hc
    have hcb : c ≠ b := Finset.ne_of_mem_erase hc
    have hc' : c ∈ s.erase a := Finset.mem_of_mem_erase hc
    have hca : c ≠ a := Finset.ne_of_mem_erase hc'
    have hcs : c ∈ s := Finset.mem_of_mem_erase hc'
    refine mem_inter.2 ⟨?_, ?_⟩
    · rw [mem_neighborFinset]
      exact hclique ha hcs (Ne.symm hca)
    · rw [mem_neighborFinset]
      exact hclique hbs hcs (Ne.symm hcb)
  have hcard2 : ((s.erase a).erase b).card = 2 := by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha, hcard]
  have := Finset.card_le_card hsub
  rw [hcard2, card_inter_neighborFinset_eq_one h hab] at this
  omega

