-- Prove2me | solution 1 for CompOT.Auction.proposition_3_7
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:40:41.488127+00:00
-- url     : https://prove2.me/submissions/92b644a6-8118-440e-a862-67af0164e0ca

import Mathlib
import Definitions.Def_CompOT_Auction_Defs

open CompOT.Auction

private theorem step_preserves_cs {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    {ε : ℝ} (hε : 0 < ε) {s s' : AuctionState n} (hc : EpsCS C ε s)
    (hs : AuctionStep C ε s s') : EpsCS C ε s' := by
  classical
  rcases hs with ⟨i, hi, j₁, j₂, hj, hmin, hsecond, hg, hS, hξ⟩
  have hdec : ∀ j, s'.g j ≤ s.g j := by
    intro j
    rw [hg]
    by_cases h : j = j₁
    · subst j
      simp only [Function.update_self]
      linarith [hmin j₂]
    · simp [Function.update_of_ne h]
  intro k hk
  rw [hS, Finset.mem_insert, Finset.mem_filter] at hk
  rcases hk with hki | ⟨hk, hkξ⟩
  · subst k
    letI : Nonempty (Fin n) := ⟨i⟩
    have hleft : C i (s'.ξ i) - s'.g (s'.ξ i) = C i j₂ - s.g j₂ + ε := by
      rw [hξ, Function.update_self, hg, Function.update_self]
      ring
    have hlow : C i j₂ - s.g j₂ ≤ ⨅ j, (C i j - s'.g j) := by
      apply le_ciInf
      intro j
      rw [hg]
      by_cases h : j = j₁
      · subst j
        simp only [Function.update_self]
        linarith
      · rw [Function.update_of_ne h]
        exact hsecond j h
    rw [hleft]
    linarith
  · have hki : k ≠ i := by
      intro h
      subst k
      exact hi hk
    have hmono : (⨅ j, (C k j - s.g j)) ≤ ⨅ j, (C k j - s'.g j) :=
      ciInf_mono (Set.finite_range _).bddBelow (fun j => sub_le_sub_left (hdec j) _)
    have hleft : C k (s'.ξ k) - s'.g (s'.ξ k) = C k (s.ξ k) - s.g (s.ξ k) := by
      rw [hξ, Function.update_of_ne hki, hg, Function.update_of_ne hkξ]
    rw [hleft]
    linarith [hc k hk]

theorem solution {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) {ε : ℝ} (hε : 0 < ε)
    (s : ℕ → AuctionState n) (T : ℕ) (hs : IsAuctionPrefix C ε s T) :
    ∀ t ≤ T, EpsCS C ε (s t) := by
  intro t
  induction t with
  | zero =>
    intro _ i hi
    simpa [hs.1] using hi
  | succ t ih =>
    intro ht
    exact step_preserves_cs C hε (ih (by omega)) (hs.2.2 t (by omega))
