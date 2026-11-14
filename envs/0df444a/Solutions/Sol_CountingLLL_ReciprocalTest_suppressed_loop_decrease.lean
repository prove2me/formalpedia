-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_loop_decrease
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:09:59.931197+00:00
-- url     : https://prove2.me/submissions/fa5c78d0-489a-409b-8340-889702263b6f

import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_first_coin_decrease
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_deterministic_transition_masses
import Theorems.Thm_CountingLLL_ReciprocalTest_suppressed_history_transition
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

/-- At a positive loop state the counter decreases within three steps with mass at least B/2. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (H : (Fin (n+1) → State) → Prop) (s : State)
    (hs : s.phase = .loop) (hi : 0 < s.i) :
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s} * (B/2) ≤
    entropyLaw B {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧
      (allSuppressedRun ω (n+3)).i < s.i} := by
  classical
  let u : State := {s with phase := .coinOracle .first}
  let H' : (Fin (n+2) → State) → Prop := fun f =>
    H (fun j : Fin (n+1) => f ⟨j.val, by omega⟩) ∧ f ⟨n, by omega⟩ = s
  have h1 := suppressed_history_transition B hB n H s u
  have hm : suppressedTransitionMass B s u = 1 := (suppressed_deterministic_transition_masses B hB s).1 hs hi
  rw [hm, mul_one] at h1
  have hphase : u.phase = .coinOracle .first := by simp [u]
  have hi' : 0 < u.i := hi
  have h2 := suppressed_first_coin_decrease B hB (n+1) H' u hphase hi'
  have hE1 : {ω | H' (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω (n+1) = u} =
      {ω | H (fun j => allSuppressedRun ω j.val) ∧ allSuppressedRun ω n = s ∧ allSuppressedRun ω (n+1) = u} := by
    ext ω; simp [H',and_assoc]
  rw [hE1,h1] at h2
  apply le_trans h2
  apply measure_mono
  intro ω hω
  rcases hω with ⟨⟨hh,hstate⟩,hnext,hless⟩
  refine ⟨hh,hstate,?_⟩
  simpa [u, Nat.add_assoc] using hless
