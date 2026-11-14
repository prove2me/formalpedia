-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_first_coin_decrease
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:07:49.895197+00:00
-- url     : https://prove2.me/submissions/3acba86e-f53f-4d7d-8777-8959d12fba96

import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_coin_zero_two_steps
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

/-- A first Coin call decreases a positive counter within two steps with probability at least B/2. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (H : (Fin (n+1) → State) → Prop) (s : State)
    (hs : s.phase = .coinOracle .first) (hi : 0 < s.i) :
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s} * (B/2) ≤
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧
      (allSuppressedRun ω (n+2)).i < s.i} := by
  classical
  have h := suppressed_coin_zero_two_steps B hB n H s .first hs
  dsimp only at h
  rw [← h]
  apply measure_mono
  intro ω hω
  obtain ⟨hh, hstate, hmid, hfinal⟩ := hω
  refine ⟨hh,hstate,?_⟩
  rw [hfinal]
  simp [coinReturn]
  omega
