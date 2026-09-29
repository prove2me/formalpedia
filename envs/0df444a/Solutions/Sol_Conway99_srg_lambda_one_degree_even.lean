-- Prove2me | solution 1 for Conway99.srg_lambda_one_degree_even
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-06T16:54:20.897504+00:00
-- url     : https://prove2.me/submissions/dd0cf6c5-b1b6-403a-aa9a-6050ab2b893f

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

open SimpleGraph Finset

/-- A finite set carrying a fixed-point-free involution has even cardinality. -/
private theorem even_card_of_involution {α : Type*} [DecidableEq α] :
    ∀ (N : ℕ) (s : Finset α) (f : α → α), s.card ≤ N →
      (∀ a ∈ s, f a ∈ s) → (∀ a ∈ s, f a ≠ a) → (∀ a ∈ s, f (f a) = a) →
      Even s.card := by
  intro N
  induction N with
  | zero =>
    intro s _ hcard _ _ _
    have hs : s.card = 0 := by omega
    simp [hs]
  | succ N ih =>
    intro s f hcard hmem hne hinv
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
    · simp
    have hfa : f a ∈ s := hmem a ha
    have hane : f a ≠ a := hne a ha
    have hfa' : f a ∈ s.erase a := Finset.mem_erase.2 ⟨hane, hfa⟩
    have hcard_t : ((s.erase a).erase (f a)).card = s.card - 2 := by
      rw [Finset.card_erase_of_mem hfa', Finset.card_erase_of_mem ha]
      omega
    have hge : 2 ≤ s.card := by
      have h1 : (s.erase a).card = s.card - 1 := Finset.card_erase_of_mem ha
      have h2 : 0 < (s.erase a).card := Finset.card_pos.2 ⟨f a, hfa'⟩
      have h3 : 0 < s.card := Finset.card_pos.2 ⟨a, ha⟩
      omega
    have hsub : ∀ b ∈ (s.erase a).erase (f a), b ∈ s ∧ b ≠ a ∧ b ≠ f a := by
      intro b hb
      rw [Finset.mem_erase, Finset.mem_erase] at hb
      exact ⟨hb.2.2, hb.2.1, hb.1⟩
    have hmem' : ∀ b ∈ (s.erase a).erase (f a), f b ∈ (s.erase a).erase (f a) := by
      intro b hb
      obtain ⟨hbs, hba, hbfa⟩ := hsub b hb
      refine Finset.mem_erase.2 ⟨?_, Finset.mem_erase.2 ⟨?_, hmem b hbs⟩⟩
      · intro hcon
        apply hba
        have := hinv b hbs
        rw [hcon, hinv a ha] at this
        exact this.symm
      · intro hcon
        apply hbfa
        have := hinv b hbs
        rw [hcon] at this
        exact this.symm
    have := ih ((s.erase a).erase (f a)) f (by omega)
      hmem' (fun b hb => hne b (hsub b hb).1) (fun b hb => hinv b (hsub b hb).1)
    rw [hcard_t] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m + 1, by omega⟩

theorem solution {V : Type*} [Fintype V] {g : SimpleGraph V}
    [DecidableRel g.Adj] {n k m : ℕ} (h : g.IsSRGWith n k 1 m) (hn : 0 < n) :
    Even k := by
  classical
  have hne : Nonempty V := by
    rw [← Fintype.card_pos_iff, h.card]; exact hn
  obtain ⟨v⟩ := hne
  set f : V → V := fun w =>
    if hx : ∃ u, g.Adj v u ∧ g.Adj w u then Classical.choose hx else w with hf
  -- the defining property of `f` on neighbours of `v`
  have key : ∀ w, g.Adj v w → g.Adj v (f w) ∧ g.Adj w (f w) := by
    intro w hw
    have hcn : Fintype.card (g.commonNeighbors v w) = 1 := h.of_adj v w hw
    have hex : ∃ u, g.Adj v u ∧ g.Adj w u := by
      have : Nonempty (g.commonNeighbors v w) := by
        rw [← Fintype.card_pos_iff, hcn]; norm_num
      obtain ⟨u, hu⟩ := this
      exact ⟨u, hu.1, hu.2⟩
    have : f w = Classical.choose hex := by
      simp only [hf, dif_pos hex]
    rw [this]
    exact Classical.choose_spec hex
  have hdeg : (g.neighborFinset v).card = k := h.regular v
  have : Even (g.neighborFinset v).card := by
    refine even_card_of_involution (g.neighborFinset v).card (g.neighborFinset v) f
      le_rfl ?_ ?_ ?_
    · intro w hw
      rw [mem_neighborFinset] at hw ⊢
      exact (key w hw).1
    · intro w hw
      rw [mem_neighborFinset] at hw
      exact fun hcon => (g.ne_of_adj (key w hw).2) hcon.symm
    · intro w hw
      rw [mem_neighborFinset] at hw
      obtain ⟨h1, h2⟩ := key w hw
      -- `w` and `f (f w)` both lie in the singleton `commonNeighbors v (f w)`
      have hcn : Fintype.card (g.commonNeighbors v (f w)) = 1 := h.of_adj v (f w) h1
      obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcn
      have hw' : w ∈ g.commonNeighbors v (f w) := ⟨hw, h2.symm⟩
      have hff : f (f w) ∈ g.commonNeighbors v (f w) :=
        ⟨(key (f w) h1).1, (key (f w) h1).2⟩
      have e1 := hx ⟨w, hw'⟩
      have e2 := hx ⟨f (f w), hff⟩
      have : (⟨f (f w), hff⟩ : g.commonNeighbors v (f w)) = ⟨w, hw'⟩ := by
        rw [e1, e2]
      simpa using this
  rwa [hdeg] at this
