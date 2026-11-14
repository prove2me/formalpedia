-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_deterministic_transition_masses
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:07:50.513492+00:00
-- url     : https://prove2.me/submissions/fdabfea9-71f4-4395-971e-7df6ad1aeb7b

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
import Theorems.Thm_CountingLLL_ReciprocalTest_encoded_read_marginals
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

/-- Suppressed uniform checks and positive-counter loop entries are deterministic. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (s : State) :
    (s.phase = .loop → 0 < s.i →
      suppressedTransitionMass B s {s with phase := .coinOracle .first} = 1) ∧
    (s.phase = .uniformCheck →
      suppressedTransitionMass B s {s with uniformUsed := s.uniformUsed+1, phase := .loop} = 1) := by
  classical
  constructor
  · intro hs hi
    have hn : s.i ≠ 0 := by omega
    simp [suppressedTransitionMass, readIndex, hs, allSuppressedStep, suppressedStep, step, hn]
  · intro hs
    have hpr := (encoded_read_marginals B hB).1 (.inr (.inr (s.j-1,s.uniformUsed)))
    letI := hpr
    have he : {v : ℕ | allSuppressedStep (uniformEntropy v) s =
        {s with uniformUsed := s.uniformUsed+1, phase := .loop}} = Set.univ := by
      ext v
      simp [allSuppressedStep, suppressedStep, hs]
    simp only [suppressedTransitionMass, readIndex, hs]
    rw [he]
    exact measure_univ
