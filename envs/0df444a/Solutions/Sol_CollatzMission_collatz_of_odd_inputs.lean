-- Prove2me | solution 1 for CollatzMission.collatz_of_odd_inputs
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T03:47:08.239407+00:00
-- url     : https://prove2.me/submissions/7834c010-e6c3-41cb-b2b4-462ad40179ae

import Definitions.Def_CollatzMission

open CollatzMission

theorem solution :
    OddInputsConjecture → ∀ n : ℕ, 0 < n → ∃ m : ℕ, collatzStep^[m] n = 1 := by
  intro hOdd n
  induction n using Nat.strongRecOn with
  | ind n ih =>
      intro hn
      by_cases hEven : Even n
      · have hn_ne_one : n ≠ 1 := by
          intro hn_one
          subst n
          norm_num at hEven
        have htwo_le : 2 ≤ n := by omega
        have hhalf_pos : 0 < n / 2 := Nat.div_pos htwo_le (by decide)
        have hhalf_lt : n / 2 < n := Nat.div_lt_self hn (by decide)
        obtain ⟨m, hm⟩ := ih (n / 2) hhalf_lt hhalf_pos
        refine ⟨m + 1, ?_⟩
        rw [Function.iterate_succ_apply]
        simpa [collatzStep, hEven] using hm
      · exact hOdd n hn hEven
