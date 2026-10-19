-- Prove2me | solution 1 for BBCode.lemma1_minimality
-- status  : ACCEPTED   (prove)
-- author  : @Winningatmath
-- created : 2026-10-16T17:59:55.35238+00:00
-- url     : https://prove2.me/submissions/18ab9c5a-2182-49e4-a92c-2670c10b2cf0

import Mathlib

theorem solution {α : Type*} [DecidableEq α]
    (checks obs : Finset (Finset α)) (z : Finset α)
    (hz : (∀ c ∈ checks, Even (z ∩ c).card) ∧ ∃ o ∈ obs, Odd (z ∩ o).card)
    (hmin : ∀ S : Finset α, ((∀ c ∈ checks, Even (S ∩ c).card) ∧
      ∃ o ∈ obs, Odd (S ∩ o).card) → z.card ≤ S.card)
    (T : Finset α) (hT : T ⊂ z) (hne : T.Nonempty) :
    ¬ ∀ c ∈ checks, Even (T ∩ c).card := by
  intro hTe
  obtain ⟨hze, o, ho, hodd⟩ := hz
  have hsub : T ⊆ z := hT.subset
  -- |(z \ T) ∩ c| + |T ∩ c| = |z ∩ c|
  have split : ∀ c : Finset α, ((z \ T) ∩ c).card + (T ∩ c).card = (z ∩ c).card := by
    intro c
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · rintro (⟨⟨hz, -⟩, hc⟩ | ⟨ht, hc⟩)
        · exact ⟨hz, hc⟩
        · exact ⟨hsub ht, hc⟩
      · rintro ⟨hz, hc⟩
        by_cases ht : x ∈ T
        · exact Or.inr ⟨ht, hc⟩
        · exact Or.inl ⟨⟨hz, ht⟩, hc⟩
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hx hx'
      exact hx.1.2 hx'.1
  have hDe : ∀ c ∈ checks, Even ((z \ T) ∩ c).card := by
    intro c hc
    have h1 := split c
    have h2 := hze c hc
    have h3 := hTe c hc
    rcases h2 with ⟨a, ha⟩
    rcases h3 with ⟨b, hb⟩
    exact ⟨a - b, by omega⟩
  have hTlt : T.card < z.card := Finset.card_lt_card hT
  have hDlt : (z \ T).card < z.card := by
    rw [Finset.card_sdiff_of_subset hsub]
    have := hne.card_pos
    omega
  have := split o
  rcases Nat.even_or_odd (T ∩ o).card with hTo | hTo
  · -- then z \ T is odd on o: a lighter logical
    have hDo : Odd ((z \ T) ∩ o).card := by
      rcases hTo with ⟨b, hb⟩
      rcases hodd with ⟨a, ha⟩
      exact ⟨a - b, by omega⟩
    have := hmin (z \ T) ⟨hDe, o, ho, hDo⟩
    omega
  · have := hmin T ⟨hTe, o, ho, hTo⟩
    omega
