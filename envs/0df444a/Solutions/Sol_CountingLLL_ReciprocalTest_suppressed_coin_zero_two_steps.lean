-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_coin_zero_two_steps
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:04:54.048475+00:00
-- url     : https://prove2.me/submissions/3311f7d3-0d52-4c72-a5f9-2e491ce87d10

import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_history_transition
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_coin_zero_transition_masses
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

/-- From any Coin oracle phase, a zero return in exactly two steps has conditional mass B/2. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (H : (Fin (n+1) → State) → Prop) (s : State) (k : Context)
    (hs : s.phase = .coinOracle k) :
    let u : State := {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k}
    let v : State := coinReturn k false {u with fairUsed := u.fairUsed+1}
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧
      allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+2) = v} =
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s} * (B/2) := by
  classical
  dsimp only
  let u : State := {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k}
  let v : State := coinReturn k false {u with fairUsed := u.fairUsed+1}
  change entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧
      allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+2) = v} = _
  let H' : (Fin (n+2) → State) → Prop := fun f =>
    H (fun j : Fin (n+1) => f ⟨j.val, by omega⟩) ∧ f ⟨n, by omega⟩ = s
  have h1 := suppressed_history_transition B hB n H s u
  have h2 := suppressed_history_transition B hB (n+1) H' u v
  have hs' : u.phase = .coinFair k := by simp [u]
  have hm1 : suppressedTransitionMass B s u = B := (suppressed_coin_zero_transition_masses B hB s k).1 hs
  have hm2 : suppressedTransitionMass B u v = 1/2 := (suppressed_coin_zero_transition_masses B hB u k).2 hs'
  rw [hm1] at h1
  rw [hm2] at h2
  have hE1 : {ω | H' (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω (n+1) = u} =
      {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = u} := by
    ext ω; simp [H',and_assoc]
  have hE2 : {ω | H' (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+1+1) = v} =
      {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = u ∧ allSuppressedRun ω (n+2) = v} := by
    ext ω; simp [H',and_assoc]
  rw [hE1,hE2,h1] at h2
  simpa [div_eq_mul_inv,mul_assoc] using h2
