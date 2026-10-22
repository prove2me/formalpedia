-- Prove2me | solution 1 for BollobasChromatic.Main.packingNum_add_edge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:49:21.59683+00:00
-- url     : https://prove2.me/submissions/c974db06-9387-493b-9b30-041158e640f3

import Mathlib
import Definitions.Def_BollobasChromatic_Main_Setting

set_option autoImplicit false
open Filter Topology Asymptotics
open BollobasChromatic.Main

noncomputable local instance (priority := 2000) W_dec {n : ℕ} (G : SimpleGraph (Fin n)) :
    DecidableRel G.Adj := fun _ _ => Classical.propDecidable _

theorem solution (n r : ℕ) (G : SimpleGraph (Fin n)) (u v : Fin n) (huv : u ≠ v) :
    packingNum G r ≤ packingNum (G ⊔ SimpleGraph.edge u v) r ∧
      packingNum (G ⊔ SimpleGraph.edge u v) r ≤ packingNum G r + 1 := by
  unfold packingNum
  constructor
  · apply Finset.sup_le
    intro F hF
    rw [Finset.mem_filter, Finset.mem_powerset] at hF
    apply Finset.le_sup (f := Finset.card)
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨fun s hs => ?_, hF.2⟩
    have := hF.1 hs
    rw [SimpleGraph.mem_cliqueFinset_iff] at this ⊢
    exact this.mono le_sup_left
  · apply Finset.sup_le
    intro F hF
    rw [Finset.mem_filter, Finset.mem_powerset] at hF
    obtain ⟨hF1, hF2⟩ := hF
    set F' : Finset (Finset (Fin n)) := F.filter (fun s => ¬ (u ∈ s ∧ v ∈ s)) with hF'
    have hmem : F' ∈ ((G.cliqueFinset r).powerset.filter
        (fun F : Finset (Finset (Fin n)) =>
          (↑F : Set (Finset (Fin n))).Pairwise (fun s t => (s ∩ t).card ≤ 1))) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨fun s hs => ?_, ?_⟩
      · rw [hF', Finset.mem_filter] at hs
        have h1 := hF1 hs.1
        rw [SimpleGraph.mem_cliqueFinset_iff] at h1 ⊢
        refine ⟨?_, h1.card_eq⟩
        intro x hx y hy hxy
        have hadj := h1.isClique hx hy hxy
        rcases hadj with h | h
        · exact h
        · rw [SimpleGraph.edge_adj] at h
          exfalso
          apply hs.2
          rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨hx, hy⟩
          · exact ⟨hy, hx⟩
      · intro s hs t ht hst
        exact hF2 (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp ht).1 hst
    have h1 := Finset.le_sup (f := Finset.card) hmem
    have h2 : (F.filter (fun s => u ∈ s ∧ v ∈ s)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro s hs t ht
      by_contra hne
      rw [Finset.mem_filter] at hs ht
      have hc := hF2 hs.1 ht.1 hne
      have hsub : ({u, v} : Finset (Fin n)) ⊆ s ∩ t := by
        intro x hx
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hs.2.1, ht.2.1⟩
        · exact Finset.mem_inter.mpr ⟨hs.2.2, ht.2.2⟩
      have := Finset.card_le_card hsub
      rw [Finset.card_pair huv] at this
      omega
    have h3 : F'.card + (F.filter (fun s => u ∈ s ∧ v ∈ s)).card = F.card := by
      rw [hF', add_comm]
      exact Finset.card_filter_add_card_filter_not (s := F) (fun s => u ∈ s ∧ v ∈ s)
    omega

