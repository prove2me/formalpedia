-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.operational_phase_probabilities
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:27:02.161928+00:00
-- url     : https://prove2.me/submissions/bc017001-31e0-4702-a553-bb13f35d0110

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
import Theorems.Thm_CountingLLL_ReciprocalTest_operational_query_fresh
import Theorems.Thm_CountingLLL_ReciprocalTest_encoded_read_marginals
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) :
    (∀ (s : State) (k : Context), s.phase = .coinOracle k →
      entropyLaw B {ω | run ω n = s ∧ ω.1 s.oracleUsed = false} =
        entropyLaw B {ω | run ω n = s} * B) ∧
    (∀ (s : State) (k : Context), s.phase = .coinFair k →
      entropyLaw B {ω | run ω n = s ∧ ω.2.1 s.fairUsed = true} =
        entropyLaw B {ω | run ω n = s} * (1/2)) ∧
    (∀ (s : State), s.phase = .uniformCheck →
      entropyLaw B {ω | run ω n = s ∧ (ω.2.2 (s.j-1,s.uniformUsed)).val = 0} =
        entropyLaw B {ω | run ω n = s} * (1/(((s.j-1)+1 : ℕ) : ℝ≥0∞))) := by
  constructor
  · intro s k hs
    have ha : readIndex s = some (.inl s.oracleUsed) := by simp [readIndex, hs]
    have h := operational_query_fresh B hB n s (.inl s.oracleUsed) ha {0}
    rw [(encoded_read_marginals B hB).2.1 s.oracleUsed] at h
    have he : {ω | run ω n = s ∧ entropyCode ω (.inl s.oracleUsed) ∈ ({0} : Set ℕ)} =
        {ω | run ω n = s ∧ ω.1 s.oracleUsed = false} := by
      ext ω
      cases hb : ω.1 s.oracleUsed <;> simp [entropyCode, hb]
    rw [he] at h
    exact h
  constructor
  · intro s k hs
    have ha : readIndex s = some (.inr (.inl s.fairUsed)) := by simp [readIndex, hs]
    have h := operational_query_fresh B hB n s (.inr (.inl s.fairUsed)) ha {1}
    rw [(encoded_read_marginals B hB).2.2.1 s.fairUsed] at h
    have he : {ω | run ω n = s ∧ entropyCode ω (.inr (.inl s.fairUsed)) ∈ ({1} : Set ℕ)} =
        {ω | run ω n = s ∧ ω.2.1 s.fairUsed = true} := by
      ext ω
      cases hb : ω.2.1 s.fairUsed <;> simp [entropyCode, hb]
    rw [he] at h
    exact h
  · intro s hs
    have ha : readIndex s = some (.inr (.inr (s.j-1,s.uniformUsed))) := by simp [readIndex, hs]
    have h := operational_query_fresh B hB n s (.inr (.inr (s.j-1,s.uniformUsed))) ha {0}
    rw [(encoded_read_marginals B hB).2.2.2 (s.j-1,s.uniformUsed)] at h
    simpa [entropyCode] using h
