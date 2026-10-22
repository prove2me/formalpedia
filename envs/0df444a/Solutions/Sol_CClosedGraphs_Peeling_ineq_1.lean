-- Prove2me | solution 1 for CClosedGraphs.Peeling.ineq_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:40:58.080725+00:00
-- url     : https://prove2.me/submissions/d654f235-8f94-4672-a654-dfed1f3dde5f

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

set_option autoImplicit false
open CClosedGraphs.Peeling

open Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Set V) (v : V) (hv : v ∈ W) :
    ((maxCliquesIn G W).filter
        (fun K => v ∈ K ∧ K.erase v ∉ maxCliquesIn G (W \ {v}))).card
      ≤ ∑ u ∈ W.toFinset.filter (fun u => u ≠ v ∧ ¬ G.Adj v u),
          numMaxCliquesIn G (W ∩ G.commonNeighbors v u) := by
  have hmem : ∀ (U : Set V) (K : Finset V), K ∈ maxCliquesIn G U ↔
      Maximal (fun T : Finset V => (↑T : Set V) ⊆ U ∧ G.IsClique (↑T : Set V)) K := by
    intro U K
    simp [maxCliquesIn]
  have hsub : ((maxCliquesIn G W).filter
        (fun K => v ∈ K ∧ K.erase v ∉ maxCliquesIn G (W \ {v}))) ⊆
      (W.toFinset.filter (fun u => u ≠ v ∧ ¬ G.Adj v u)).biUnion
        (fun u => (maxCliquesIn G (W ∩ G.commonNeighbors v u)).image (insert v)) := by
    intro K hK
    simp only [Finset.mem_filter] at hK
    obtain ⟨hKmax, hvK, hnot⟩ := hK
    rw [hmem] at hKmax
    obtain ⟨⟨hKW, hKcl⟩, hKm⟩ := hKmax
    -- the clique K.erase v is not maximal in W \ {v}
    have hP : (↑(K.erase v) : Set V) ⊆ W \ {v} ∧ G.IsClique (↑(K.erase v) : Set V) := by
      refine ⟨?_, ?_⟩
      · intro x hx
        have hx' : x ∈ K.erase v := hx
        rw [Finset.mem_erase] at hx'
        exact ⟨hKW hx'.2, hx'.1⟩
      · exact hKcl.subset (by
          intro x hx
          have hx' : x ∈ K.erase v := hx
          exact (Finset.mem_erase.1 hx').2)
    have hnm : ¬ Maximal (fun T : Finset V => (↑T : Set V) ⊆ W \ {v} ∧ G.IsClique (↑T : Set V))
        (K.erase v) := by
      intro h
      exact hnot ((hmem _ _).2 h)
    have hex : ∃ y : Finset V, ((↑y : Set V) ⊆ W \ {v} ∧ G.IsClique (↑y : Set V)) ∧
        K.erase v ≤ y ∧ ¬ y ≤ K.erase v := by
      by_contra hcon
      push_neg at hcon
      exact hnm ⟨hP, fun y hy hle => hcon y hy hle⟩
    obtain ⟨y, ⟨hyW, hycl⟩, hKy, hyK⟩ := hex
    rw [Finset.not_subset] at hyK
    obtain ⟨u, huy, huK⟩ := hyK
    have huW : u ∈ W := (hyW huy).1
    have huv : u ≠ v := by
      intro h
      exact (hyW huy).2 (by simpa using h)
    have hadj : ∀ x ∈ K.erase v, G.Adj u x := by
      intro x hx
      have hxy : x ∈ y := hKy hx
      have hux : u ≠ x := by
        intro h; subst h; exact huK hx
      exact hycl huy hxy hux
    have hnadj : ¬ G.Adj v u := by
      intro hvu
      have hcl : G.IsClique (↑(insert u K) : Set V) := by
        rw [Finset.coe_insert]
        refine hKcl.insert ?_
        intro b hb hub
        by_cases hbv : b = v
        · subst hbv; exact hvu.symm
        · exact hadj b (Finset.mem_erase.2 ⟨hbv, hb⟩)
      have hle : insert u K ≤ K := hKm ⟨by
        intro x hx
        rw [Finset.coe_insert] at hx
        rcases hx with rfl | hx
        · exact huW
        · exact hKW hx, hcl⟩ (Finset.subset_insert u K)
      have : u ∈ K := hle (Finset.mem_insert_self u K)
      exact huK (Finset.mem_erase.2 ⟨huv, this⟩)
    rw [Finset.mem_biUnion]
    refine ⟨u, ?_, ?_⟩
    · simp only [Finset.mem_filter, Set.mem_toFinset]
      exact ⟨huW, huv, hnadj⟩
    · rw [Finset.mem_image]
      refine ⟨K.erase v, ?_, Finset.insert_erase hvK⟩
      rw [hmem]
      refine ⟨⟨?_, hP.2⟩, ?_⟩
      · intro x hx
        have hx' : x ∈ K.erase v := hx
        rw [Finset.mem_erase] at hx'
        refine ⟨hKW hx'.2, ?_, ?_⟩
        · exact hKcl hvK hx'.2 (Ne.symm hx'.1)
        · exact hadj x (Finset.mem_erase.2 hx')
      · intro y' hy' hle
        have hcl : G.IsClique (↑(insert v y') : Set V) := by
          rw [Finset.coe_insert]
          refine hy'.2.insert ?_
          intro b hb hvb
          exact (hy'.1 hb).2.1
        have hle2 : insert v y' ≤ K := hKm ⟨by
          intro x hx
          rw [Finset.coe_insert] at hx
          rcases hx with rfl | hx
          · exact hv
          · exact (hy'.1 hx).1, hcl⟩ (by
            intro x hx
            rw [Finset.mem_insert]
            by_cases hxv : x = v
            · left; exact hxv
            · right; exact hle (Finset.mem_erase.2 ⟨hxv, hx⟩))
        intro x hx
        have hxv : x ≠ v := by
          intro h
          have := (hy'.1 hx).2.1
          subst h
          exact G.loopless.irrefl _ this
        exact Finset.mem_erase.2 ⟨hxv, hle2 (Finset.mem_insert_of_mem hx)⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun u _ => Finset.card_image_le)
