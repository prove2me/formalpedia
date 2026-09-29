-- Prove2me | solution 1 for CollatzMission.collatz_of_no_cycles_and_no_divergence
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T03:48:22.775821+00:00
-- url     : https://prove2.me/submissions/7e1447c3-17a1-4218-948b-61857897fe3f

import Definitions.Def_CollatzMission

open CollatzMission

theorem solution :
    NoEventualCycleCounterexamples →
      NoDivergentCounterexamples →
        ∀ n : ℕ, 0 < n → ∃ m : ℕ, collatzStep^[m] n = 1 := by
  intro hCycles hDivergence n hn
  by_contra hReaches
  have hAvoids : OrbitAvoidsOne n := by
    intro k hk
    exact hReaches ⟨k, hk⟩
  by_cases hCycle : EventualCycleCounterexample n
  · exact hCycles n hn hCycle
  · exact hDivergence n hn ⟨hAvoids, hCycle⟩
