-- Prove2me | solution 1 for CompOT.Auction.properties_b_c
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:41:23.95232+00:00
-- url     : https://prove2.me/submissions/b657d171-fc6f-49b5-b30a-d721674cb5d2

import Mathlib
import Definitions.Def_CompOT_Auction_Defs

open CompOT.Auction

private theorem step_injective {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) {s s' : AuctionState n}
    (hinj : ∀ a ∈ s.S, ∀ b ∈ s.S, s.ξ a = s.ξ b → a = b)
    (hs : AuctionStep C ε s s') :
    ∀ a ∈ s'.S, ∀ b ∈ s'.S, s'.ξ a = s'.ξ b → a = b := by
  rcases hs with ⟨i, hi, j₁, j₂, hj, hmin, hsecond, hg, hS, hξ⟩
  intro a ha b hb hab
  rw [hS, Finset.mem_insert, Finset.mem_filter] at ha hb
  rcases ha with hai | ⟨ha, haξ⟩
  · subst a
    rcases hb with hbi | ⟨hb, hbξ⟩
    · exact hbi.symm
    · have hbi : b ≠ i := fun h => hi (h ▸ hb)
      have heq : j₁ = s.ξ b := by
        simpa only [hξ, Function.update_self, Function.update_of_ne hbi] using hab
      exact False.elim (hbξ heq.symm)
  · have hai : a ≠ i := fun h => hi (h ▸ ha)
    rcases hb with hbi | ⟨hb, hbξ⟩
    · subst b
      have heq : s.ξ a = j₁ := by
        simpa only [hξ, Function.update_self, Function.update_of_ne hai] using hab
      exact False.elim (haξ heq)
    · have hbi : b ≠ i := fun h => hi (h ▸ hb)
      apply hinj a ha b hb
      simpa only [hξ, Function.update_of_ne hai, Function.update_of_ne hbi] using hab

private theorem run_injective {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (ε : ℝ) (s : ℕ → AuctionState n) (T : ℕ) (hs : IsAuctionPrefix C ε s T) :
    ∀ t ≤ T, ∀ a ∈ (s t).S, ∀ b ∈ (s t).S, (s t).ξ a = (s t).ξ b → a = b := by
  intro t
  induction t with
  | zero =>
    intro _ a ha
    simpa [hs.1] using ha
  | succ t ih =>
    intro ht
    exact step_injective C ε (ih (by omega)) (hs.2.2 t (by omega))

theorem solution {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε)
    (s : ℕ → AuctionState n) (T : ℕ) (hs : IsAuctionPrefix C ε s T) :
    ∀ t < T, (s t).S.card ≤ (s (t + 1)).S.card ∧
      (∃ j, (s (t + 1)).g j ≤ (s t).g j - ε) ∧
      ∀ j, (s (t + 1)).g j ≤ (s t).g j := by
  classical
  intro t ht
  have hinj := run_injective C ε s T hs t (by omega)
  rcases hs.2.2 t ht with ⟨i, hi, j₁, j₂, hj, hmin, hsecond, hg, hS, hξ⟩
  have hdrop : (s (t + 1)).g j₁ ≤ (s t).g j₁ - ε := by
    rw [hg, Function.update_self]
    linarith [hmin j₂]
  refine ⟨?_, ⟨j₁, hdrop⟩, ?_⟩
  · have hni : i ∉ (s t).S.filter (fun a => (s t).ξ a ≠ j₁) :=
      fun h => hi (Finset.mem_filter.mp h).1
    rw [hS, Finset.card_insert_of_notMem hni]
    by_cases he : ∃ a ∈ (s t).S, (s t).ξ a = j₁
    · rcases he with ⟨a, ha, hξa⟩
      have hfilter : (s t).S.filter (fun b => (s t).ξ b ≠ j₁) = (s t).S.erase a := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hb, hbξ⟩
          exact ⟨fun h => hbξ (h ▸ hξa), hb⟩
        · rintro ⟨hba, hb⟩
          exact ⟨hb, fun h => hba (hinj b hb a ha (h.trans hξa.symm))⟩
      rw [hfilter, Finset.card_erase_of_mem ha]
      have hpos : 0 < (s t).S.card := Finset.card_pos.mpr ⟨a, ha⟩
      omega
    · have hfilter : (s t).S.filter (fun a => (s t).ξ a ≠ j₁) = (s t).S := by
        apply Finset.filter_eq_self.mpr
        intro a ha h
        exact he ⟨a, ha, h⟩
      rw [hfilter]
      omega
  · intro j
    by_cases h : j = j₁
    · subst j
      linarith
    · rw [hg, Function.update_of_ne h]
