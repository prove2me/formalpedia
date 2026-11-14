-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.full_suppressed_ignores_return_entropy
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:48:24.444135+00:00
-- url     : https://prove2.me/submissions/149bb8f8-d5b5-4f7d-bc88-c41154999851

import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
set_option autoImplicit false
open CountingLLL.ReciprocalTest

private theorem fair_mono (ω : Entropy) (s : State) : s.fairUsed ≤ (allSuppressedStep ω s).fairUsed := by
  cases hs : s.phase with
  | start => simp [allSuppressedStep,hs]
  | initialCheck => simp [allSuppressedStep,suppressedStep,hs]
  | loop => simp only [allSuppressedStep,suppressedStep,step,hs]; split <;> simp
  | coinOracle k => cases k <;> simp only [allSuppressedStep,suppressedStep,step,hs] <;> split <;> simp [coinReturn]
  | coinFair k => cases k <;> simp only [allSuppressedStep,suppressedStep,step,hs] <;> split <;> simp [coinReturn]
  | uniformCheck => simp [allSuppressedStep,suppressedStep,hs]
  | done b => simp [allSuppressedStep,suppressedStep,step,hs]

private theorem fair_positive (ω : Entropy) (n : ℕ) : 1 ≤ (allSuppressedRun ω (n+1)).fairUsed := by
  induction n with
  | zero => simp [allSuppressedRun,allSuppressedStep,initial]
  | succ n ih =>
    have hr : allSuppressedRun ω (n+1+1) = allSuppressedStep ω (allSuppressedRun ω (n+1)) := by
      simp [allSuppressedRun, Function.iterate_succ_apply']
    rw [hr]
    exact le_trans ih (fair_mono ω _)

private theorem step_ext (ω ω' : Entropy) (s : State) (hpos : 1 ≤ s.fairUsed)
    (ho : ω.1 = ω'.1) (hf : ∀ k ≥ 1, ω.2.1 k = ω'.2.1 k) :
    allSuppressedStep ω s = allSuppressedStep ω' s := by
  have hbit := hf s.fairUsed hpos
  cases hs : s.phase <;> simp [allSuppressedStep,suppressedStep,step,hs,ho,hbit]

/-- The fully suppressed path ignores the first fair bit and all uniform-return bits. -/
theorem solution (ω ω' : Entropy)
    (ho : ω.1 = ω'.1) (hf : ∀ k ≥ 1, ω.2.1 k = ω'.2.1 k) (n : ℕ) :
    allSuppressedRun ω n = allSuppressedRun ω' n := by
  cases n with
  | zero => rfl
  | succ n =>
    induction n with
    | zero => simp [allSuppressedRun,allSuppressedStep,initial]
    | succ n ih =>
      have hr (ξ : Entropy) : allSuppressedRun ξ (n+1+1) = allSuppressedStep ξ (allSuppressedRun ξ (n+1)) := by
        simp [allSuppressedRun, Function.iterate_succ_apply']
      rw [hr,hr,← ih]
      exact step_ext ω ω' _ (fair_positive ω n) ho hf
