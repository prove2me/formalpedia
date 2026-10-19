-- Prove2me | solution 1 for BnBPEP.WeakCvx.eq_44_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:25:39.56292+00:00
-- url     : https://prove2.me/submissions/d0662a15-0055-4318-9c2e-75a208d28bf2

import Mathlib
set_option autoImplicit false

theorem solution (N : ℕ) (h : ℝ) (hh0 : 0 < h) (hh : h ≤ 1 / 2) (b : ℕ → ℝ)
    (hrec : ∀ k ≤ N, 4 + (1 - 2 * h) * b (k + 1) = b k) (hterm : b (N + 1) = 0) :
    (∀ k ≤ N + 1, b k = 2 / h * (1 - (1 - 2 * h) ^ (N + 1 - k)) ∧ 0 ≤ b k) ∧
      (∀ k ≤ N, 0 ≤ h ^ 2 * b (k + 1) ∧ 0 ≤ 2 * h * b (k + 1) ∧ 0 ≤ b k - b (k + 1)) := by
  have hne : h ≠ 0 := hh0.ne'
  have hr0 : 0 ≤ 1 - 2 * h := by linarith
  have hr1 : 1 - 2 * h ≤ 1 := by linarith
  have key : ∀ j : ℕ, j ≤ N + 1 → b (N + 1 - j) = (2 / h) * (1 - (1 - 2 * h) ^ j) := by
    intro j
    induction j with
    | zero => intro _; simp [hterm]
    | succ j ih =>
      intro hj
      have h1 : N + 1 - (j + 1) ≤ N := by omega
      have h2 : N + 1 - (j + 1) + 1 = N + 1 - j := by omega
      have := hrec _ h1
      rw [h2, ih (by omega)] at this
      rw [← this]
      field_simp
      ring
  have closed : ∀ k ≤ N + 1, b k = 2 / h * (1 - (1 - 2 * h) ^ (N + 1 - k)) := by
    intro k hk
    have := key (N + 1 - k) (by omega)
    have e : N + 1 - (N + 1 - k) = k := by omega
    rwa [e] at this
  have nonneg : ∀ k ≤ N + 1, 0 ≤ b k := by
    intro k hk
    rw [closed k hk]
    have : (1 - 2 * h) ^ (N + 1 - k) ≤ 1 := pow_le_one₀ hr0 hr1
    have : 0 ≤ 2 / h := by positivity
    apply mul_nonneg this
    linarith
  refine ⟨fun k hk => ⟨closed k hk, nonneg k hk⟩, fun k hk => ⟨?_, ?_, ?_⟩⟩
  · exact mul_nonneg (by positivity) (nonneg _ (by omega))
  · exact mul_nonneg (by positivity) (nonneg _ (by omega))
  · have e := hrec k hk
    rw [closed (k + 1) (by omega)] at e
    have h3 : (1 - 2 * h) ^ (N + 1 - (k + 1)) * (1 - 2 * h) = (1 - 2 * h) ^ (N + 1 - k) := by
      rw [← pow_succ]; congr 1; omega
    have hb : b k - b (k + 1) = 4 * (1 - 2 * h) ^ (N + 1 - (k + 1)) := by
      rw [closed (k + 1) (by omega), ← e]
      field_simp
      ring
    rw [hb]
    positivity
