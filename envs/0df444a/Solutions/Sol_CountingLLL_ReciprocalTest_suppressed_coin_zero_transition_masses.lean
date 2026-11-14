-- Prove2me | solution 1 for CountingLLL.ReciprocalTest.suppressed_coin_zero_transition_masses
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T11:03:44.71667+00:00
-- url     : https://prove2.me/submissions/af7c0aea-ff0b-4ff7-947b-1d6ab3171574

import Definitions.Def_CountingLLL_ReciprocalSuppressedTransition
import Theorems.Thm_CountingLLL_ReciprocalTest_encoded_read_marginals
set_option autoImplicit false
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

/-- Explicit masses of the two transitions making a Coin call return zero. -/
theorem solution (B : ℝ≥0∞) (hB : B ≤ 1) (s : State) (k : Context) :
    (s.phase = .coinOracle k →
      suppressedTransitionMass B s {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k} = B) ∧
    (s.phase = .coinFair k →
      suppressedTransitionMass B s (coinReturn k false {s with fairUsed := s.fairUsed+1}) = 1/2) := by
  classical
  constructor
  · intro hs
    have he : {v : ℕ | allSuppressedStep (uniformEntropy v) s =
        {s with oracleUsed := s.oracleUsed+1, phase := .coinFair k}} = {0} := by
      ext v
      by_cases hv : v = 0 <;> cases k <;>
        simp [allSuppressedStep,suppressedStep,step,hs,uniformEntropy,coinReturn,hv]
    simp only [suppressedTransitionMass,readIndex,hs]
    rw [he]
    exact (encoded_read_marginals B hB).2.1 s.oracleUsed
  · intro hs
    have he : {v : ℕ | allSuppressedStep (uniformEntropy v) s =
        coinReturn k false {s with fairUsed := s.fairUsed+1}} = {v | v ≠ 0} := by
      ext v
      by_cases hv : v = 0 <;> cases k <;>
        simp [allSuppressedStep,suppressedStep,step,hs,uniformEntropy,coinReturn,hv]
    simp only [suppressedTransitionMass,readIndex,hs]
    rw [hs] at he
    rw [he]
    change (fairLaw.map bitCode) {v : ℕ | v ≠ 0} = 1/2
    rw [Measure.map_apply (measurable_of_countable bitCode) (Set.to_countable _).measurableSet]
    have he' : bitCode ⁻¹' {v : ℕ | v ≠ 0} = {true} := by ext b; cases b <;> simp [bitCode]
    rw [he']
    simp [fairLaw]
