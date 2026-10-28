-- Prove2me | solution 1 for FinancialDerivatives.FD05.upperKnockOutTree_mono_barrier
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:41:04.359033+00:00
-- url     : https://prove2.me/submissions/c2a5f56d-10b9-40a8-9823-ef3e930b2b12

import Mathlib.Data.Real.Basic
import Definitions.Def_fd03_payoffTreeLe
import Definitions.Def_fd05_upperKnockOutTree

open FinancialDerivatives.FD03 FinancialDerivatives.FD05


theorem A3FD_mono_barrier (m : BinomialMarket) (B₁ B₂ : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hB : B₁ ≤ B₂) (hg : ∀ S : ℝ, 0 ≤ g S) :
    ∀ (n t : ℕ) (S : ℝ) (h1 h2 : Bool), (h2 = true → h1 = true) →
    payoffTreeLe n (upperKnockOutTree m B₁ monitor g n t S h1)
      (upperKnockOutTree m B₂ monitor g n t S h2) := by
  have hT : ∀ (S : ℝ) (t : ℕ) (h1 h2 : Bool), (h2 = true → h1 = true) →
      (h2 || upperTouch B₂ S monitor t) = true → (h1 || upperTouch B₁ S monitor t) = true := by
    intro S t h1 h2 hh h
    simp only [Bool.or_eq_true, upperTouch, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    rcases h with h | ⟨h, h'⟩
    · exact Or.inl (hh h)
    · exact Or.inr ⟨h, hB.trans h'⟩
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
    (N : ℕ) (B₁ B₂ : ℝ) (monitor : ℕ → Bool) (g : ℝ → ℝ)
    (hB : B₁ ≤ B₂) (hg : ∀ S : ℝ, 0 ≤ g S) :
    payoffTreeLe N
      (upperKnockOutTree m B₁ monitor g N 0 m.initialSpot false)
      (upperKnockOutTree m B₂ monitor g N 0 m.initialSpot false) := by
  exact A3FD_mono_barrier m B₁ B₂ monitor g hB hg N 0 m.initialSpot false false id
