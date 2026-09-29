-- Prove2me | solution 1 for Finset.path3_count_le_triple_rep_count
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:43.81306+00:00
-- url     : https://prove2.me/submissions/eff9b131-e7e4-43f9-86dc-bc930e563bc1

import Mathlib

open scoped Pointwise

open Finset in
theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (E : Finset (G × G)) (hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S)
    (a b : G) :
    (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
    ≤ ((S ×ˢ S ×ˢ S).filter
        fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card := by
  -- Define the map (b₁, a₁) ↦ (a + b₁, a₁ + b₁, a₁ + b).
  set f : G × G → G × G × G := fun q ↦ (a + q.1, q.2 + q.1, q.2 + b) with hf_def
  set src : Finset (G × G) :=
    (B ×ˢ A).filter (fun q : G × G ↦
      (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E) with hsrc_def
  set tgt : Finset (G × G × G) :=
    (S ×ˢ S ×ˢ S).filter (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)
    with htgt_def
  apply Finset.card_le_card_of_injOn f
  · -- MapsTo: f sends src into tgt.
    intro q hq
    simp only [hsrc_def, Finset.coe_filter, Set.mem_ofPred_eq,
      Finset.mem_product] at hq
    obtain ⟨⟨_hq1B, _hq2A⟩, hEab1, hEa1b1, hEa1b⟩ := hq
    have hs1 : a + q.1 ∈ S := hSdef (a, q.1) hEab1
    have hs2 : q.2 + q.1 ∈ S := hSdef (q.2, q.1) hEa1b1
    have hs3 : q.2 + b ∈ S := hSdef (q.2, b) hEa1b
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_product.mpr ⟨hs1, Finset.mem_product.mpr ⟨hs2, hs3⟩⟩
    · -- (a + b₁) - (a₁ + b₁) + (a₁ + b) = a + b.
      show (a + q.1) - (q.2 + q.1) + (q.2 + b) = a + b
      abel
  · -- InjOn: f is injective on src.
    intro q₁ _hq₁ q₂ _hq₂ hfeq
    -- f q₁ = f q₂ means (a + q₁.1, q₁.2 + q₁.1, q₁.2 + b) = (a + q₂.1, …, q₂.2 + b).
    -- Project out the first and third coordinates of the triple equality.
    have h1 : a + q₁.1 = a + q₂.1 := by
      have := congrArg Prod.fst hfeq
      simpa [hf_def] using this
    have h3 : q₁.2 + b = q₂.2 + b := by
      have := congrArg (fun p : G × G × G ↦ p.2.2) hfeq
      simpa [hf_def] using this
    have hq1eq : q₁.1 = q₂.1 := add_left_cancel h1
    have hq2eq : q₁.2 = q₂.2 := add_right_cancel h3
    exact Prod.ext hq1eq hq2eq
