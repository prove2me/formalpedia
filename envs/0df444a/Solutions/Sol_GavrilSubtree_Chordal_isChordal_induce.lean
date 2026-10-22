-- Prove2me | solution 1 for GavrilSubtree.Chordal.isChordal_induce
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:56:35.135097+00:00
-- url     : https://prove2.me/submissions/3e286b38-3fe1-4369-80be-7e4126f7b1f1

import Mathlib
import Definitions.Def_GavrilSubtree_Chordal_Setting

set_option autoImplicit false
open GavrilSubtree.Chordal

universe u

theorem gsc_induce {V : Type u} (G : SimpleGraph V) (hG : IsChordal G) (s : Set V) :
    IsChordal (G.induce s) := by
  intro u c hc h4
  let e : G.induce s ↪g G := SimpleGraph.Embedding.induce s
  let f : G.induce s →g G := e.toHom
  have hf : Function.Injective f := e.injective
  have hc' : (c.map f).IsCycle := (SimpleGraph.Walk.isCycle_map_iff_of_injective hf).2 hc
  have hl : 4 ≤ (c.map f).length := by rw [SimpleGraph.Walk.length_map]; exact h4
  obtain ⟨x, hx, y, hy, hadj, hnot⟩ := hG _ (c.map f) hc' hl
  rw [SimpleGraph.Walk.support_map, List.mem_map] at hx hy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  refine ⟨x', hx', y', hy', hadj, ?_⟩
  intro hmem
  apply hnot
  rw [SimpleGraph.Walk.edges_map]
  exact List.mem_map.2 ⟨s(x', y'), hmem, rfl⟩

theorem gsc_inter {V : Type u} {G : SimpleGraph V} {β : Type u}
    {T : SimpleGraph β} {F : V → Set β} (hF : IsSubtreeRep G T F) (A₁ A₂ : Cliques G)
    (hne : A₁ ≠ A₂) :
    (⋂ v ∈ A₁.1, F v) ∩ (⋂ v ∈ A₂.1, F v) = ∅ := by
  by_contra hcon
  obtain ⟨x, hx1, hx2⟩ := Set.nonempty_iff_ne_empty.2 hcon
  rw [Set.mem_iInter₂] at hx1 hx2
  have hadj : ∀ u ∈ A₁.1, ∀ v ∈ A₂.1, u ≠ v → G.Adj u v := by
    intro u hu v hv huv
    exact (hF.2.2 u v huv).2 ⟨x, hx1 u hu, hx2 v hv⟩
  have hcl : G.IsClique (A₁.1 ∪ A₂.1) := by
    intro u hu v hv huv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact A₁.2.1 hu hv huv
    · exact hadj u hu v hv huv
    · exact (hadj v hv u hu huv.symm).symm
    · exact A₂.2.1 hu hv huv
  have h1 : A₁.1 ∪ A₂.1 ≤ A₁.1 := A₁.2.2 hcl Set.subset_union_left
  have h2 : A₁.1 ∪ A₂.1 ≤ A₂.1 := A₂.2.2 hcl Set.subset_union_right
  apply hne
  apply Subtype.ext
  apply Set.Subset.antisymm
  · exact Set.subset_union_left.trans h2
  · exact Set.subset_union_right.trans h1

theorem solution {V : Type u} (G : SimpleGraph V) (hG : IsChordal G) (s : Set V) :
    IsChordal (G.induce s) := gsc_induce G hG s
