-- Prove2me | solution 1 for FourColourRSST.Ring.consistent_closure
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:21:14.109826+00:00
-- url     : https://prove2.me/submissions/f6988047-2c25-4bfc-94a0-8527c76f0ef1

import Mathlib
import Definitions.Def_FourColourRSST_Ring_Setting
set_option autoImplicit false
open FourColourRSST.Ring

private theorem union_consistent {k : ℕ} [NeZero k]
    (F : Set (Set (EdgeColouring k))) (hF : ∀ C ∈ F, Consistent C) :
    Consistent (⋃₀ F) := by
  intro κ hκ θ
  obtain ⟨C, hC, hκ⟩ := hκ
  obtain ⟨M, hm, hf, hall⟩ := hF C hC κ hκ θ
  exact ⟨M, hm, hf, fun κ' h => Set.mem_sUnion.mpr ⟨C, hC, hall κ' h⟩⟩

theorem solution {k : ℕ} [NeZero k] (hk : 3 ≤ k) :
    Consistent (∅ : Set (EdgeColouring k)) ∧
    (∀ C₁ C₂ : Set (EdgeColouring k), Consistent C₁ → Consistent C₂ → Consistent (C₁ ∪ C₂)) ∧
    (∀ S : Set (EdgeColouring k), ∃! S' : Set (EdgeColouring k),
      S' ⊆ S ∧ Consistent S' ∧ ∀ T ⊆ S, Consistent T → T ⊆ S') := by
  refine ⟨?_, ?_, ?_⟩
  · intro κ hκ
    exact False.elim hκ
  · intro C₁ C₂ h₁ h₂ κ hκ θ
    rcases hκ with hκ | hκ
    · obtain ⟨M, hm, hf, hall⟩ := h₁ κ hκ θ
      exact ⟨M, hm, hf, fun κ' h => Or.inl (hall κ' h)⟩
    · obtain ⟨M, hm, hf, hall⟩ := h₂ κ hκ θ
      exact ⟨M, hm, hf, fun κ' h => Or.inr (hall κ' h)⟩
  · intro S
    let F : Set (Set (EdgeColouring k)) := {T | T ⊆ S ∧ Consistent T}
    have hs : ⋃₀ F ⊆ S := by
      intro κ hκ
      obtain ⟨T, hT, hκ⟩ := hκ
      exact hT.1 hκ
    have hc : Consistent (⋃₀ F) := union_consistent F (fun T hT => hT.2)
    have hg : ∀ T ⊆ S, Consistent T → T ⊆ ⋃₀ F := by
      intro T hT hc κ hκ
      exact Set.mem_sUnion.mpr ⟨T, ⟨hT, hc⟩, hκ⟩
    refine ⟨⋃₀ F, ⟨hs, hc, hg⟩, ?_⟩
    intro T hT
    exact Set.Subset.antisymm (hg T hT.1 hT.2.1) (hT.2.2 _ hs hc)

#print axioms solution
