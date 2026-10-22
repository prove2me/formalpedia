-- Prove2me | solution 1 for CClosedGraphs.Peeling.types_one_two_le
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:39:11.240265+00:00
-- url     : https://prove2.me/submissions/7dd3a1ca-400a-4380-886f-54dd46da03dc

import Mathlib
import Definitions.Def_CClosedGraphs_Peeling_Setting

set_option autoImplicit false
open CClosedGraphs.Peeling

open Classical in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Set V) (v : V) (hv : v ∈ W) :
    ((maxCliquesIn G W).filter
        (fun K => v ∉ K ∨ K.erase v ∈ maxCliquesIn G (W \ {v}))).card
      ≤ numMaxCliquesIn G (W \ {v}) := by
  have hmem : ∀ (U : Set V) (K : Finset V), K ∈ maxCliquesIn G U ↔
      Maximal (fun T : Finset V => (↑T : Set V) ⊆ U ∧ G.IsClique (↑T : Set V)) K := by
    intro U K
    simp [maxCliquesIn]
  unfold numMaxCliquesIn
  apply Finset.card_le_card_of_injOn (fun K => K.erase v)
  · intro K hK
    simp only [Finset.mem_coe, Finset.mem_filter] at hK ⊢
    obtain ⟨hKmax, hor⟩ := hK
    by_cases hvK : v ∈ K
    · rcases hor with h | h
      · exact absurd hvK h
      · exact h
    · rw [Finset.erase_eq_of_notMem hvK]
      rw [hmem] at hKmax ⊢
      obtain ⟨⟨hsub, hcl⟩, hmax⟩ := hKmax
      refine ⟨⟨?_, hcl⟩, ?_⟩
      · intro x hx
        refine ⟨hsub hx, ?_⟩
        intro hxv
        rw [Set.mem_singleton_iff] at hxv
        subst hxv
        exact hvK (by exact_mod_cast hx)
      · intro y hy hKy
        exact hmax ⟨fun x hx => (hy.1 hx).1, hy.2⟩ hKy
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter] at ha hb
    have key : ∀ a b : Finset V, a ∈ maxCliquesIn G W → b ∈ maxCliquesIn G W → v ∉ a → v ∈ b →
        a.erase v = b.erase v → False := by
      intro a b ha hb hva hvb hab
      rw [Finset.erase_eq_of_notMem hva] at hab
      rw [hmem] at ha hb
      have hle : a ≤ b := by
        rw [hab]; exact Finset.erase_subset v b
      have := ha.2 hb.1 hle
      exact hva (this hvb)
    by_cases hva : v ∈ a
    · by_cases hvb : v ∈ b
      · rw [← Finset.insert_erase hva, ← Finset.insert_erase hvb]
        simp only at hab
        rw [hab]
      · exact (key b a hb.1 ha.1 hvb hva hab.symm).elim
    · by_cases hvb : v ∈ b
      · exact (key a b ha.1 hb.1 hva hvb hab).elim
      · simp only at hab
        rwa [Finset.erase_eq_of_notMem hva, Finset.erase_eq_of_notMem hvb] at hab
