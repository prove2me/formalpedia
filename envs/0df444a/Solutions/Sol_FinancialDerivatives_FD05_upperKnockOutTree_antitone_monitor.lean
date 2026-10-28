-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperKnockOutTree_antitone_monitor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:41:08.056335+00:00
-- url     : https://prove2.me/submissions/54a5f40f-c4d5-4cf2-8f09-a9f4dabc8573

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_payoffTreeLe
import Definitions.Def_fd05_upperKnockOutTree

open FinancialDerivatives.FD03 FinancialDerivatives.FD05


theorem A3FD_antitone_monitor (m : BinomialMarket) (B : ℝ) (M₁ M₂ : ℕ → Bool) (g : ℝ → ℝ)
    (hM : ∀ t : ℕ, M₁ t = true → M₂ t = true) (hg : ∀ S : ℝ, 0 ≤ g S) :
    ∀ (n t : ℕ) (S : ℝ) (h1 h2 : Bool), (h2 = true → h1 = true) →
    payoffTreeLe n (upperKnockOutTree m B M₂ g n t S h1)
      (upperKnockOutTree m B M₁ g n t S h2) := by
  have hT : ∀ (S : ℝ) (t : ℕ) (h1 h2 : Bool), (h2 = true → h1 = true) →
      (h2 || upperTouch B S M₁ t) = true → (h1 || upperTouch B S M₂ t) = true := by
    intro S t h1 h2 hh h
    simp only [Bool.or_eq_true, upperTouch, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | ⟨h, h'⟩
    · exact Or.inl (hh h)
    · exact Or.inr ⟨hM t h, h'⟩
  intro n
  induction n with
  | zero =>
    intro t S h1 h2 hh
    simp only [upperKnockOutTree, payoffTreeLe]
    have := hT S t h1 h2 hh
    split_ifs with c1 c2 <;> simp_all
  | succ n ih =>
    intro t S h1 h2 hh
    simp only [upperKnockOutTree, payoffTreeLe]
    exact ⟨ih _ _ _ _ (hT S t h1 h2 hh), ih _ _ _ _ (hT S t h1 h2 hh)⟩

theorem solution (m : BinomialMarket)
    (N : ℕ) (B : ℝ) (M₁ M₂ : ℕ → Bool) (g : ℝ → ℝ)
    (hM : ∀ t : ℕ, M₁ t = true → M₂ t = true)
    (hg : ∀ S : ℝ, 0 ≤ g S) :
    payoffTreeLe N
      (upperKnockOutTree m B M₂ g N 0 m.initialSpot false)
      (upperKnockOutTree m B M₁ g N 0 m.initialSpot false) := by
  exact A3FD_antitone_monitor m B M₁ M₂ g hM hg N 0 m.initialSpot false false id
