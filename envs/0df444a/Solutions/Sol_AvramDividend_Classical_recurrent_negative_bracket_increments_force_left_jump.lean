-- Prove2me | solution 1 for AvramDividend.Classical.recurrent_negative_bracket_increments_force_left_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:20:40.026796+00:00
-- url     : https://prove2.me/submissions/19e12438-e88d-43c1-be85-a87aa4e5bcd3

import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped NNReal

/-- A convergent path-bracket sequence with arbitrarily late negative
decrements forces the limiting left-to-right jump to exceed the threshold
weakly. The strict/weak distinction matters at boundary atoms. -/
theorem solution
    (s u : ℕ → ℝ≥0) (f : ℝ≥0 → ℝ)
    (t : ℝ≥0) (left a : ℝ)
    (hs : Tendsto (fun n => f (s n)) atTop (nhds left))
    (hu : Tendsto (fun n => f (u n)) atTop (nhds (f t)))
    (hrec : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      f (u n) - f (s n) < -a) :
    f t - left ≤ -a := by
  by_contra hle
  have hgt : -a < f t - left := lt_of_not_ge hle
  have hlim : Tendsto (fun n : ℕ => f (u n) - f (s n))
      atTop (nhds (f t - left)) := hu.sub hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim.eventually (Ioi_mem_nhds hgt))
  obtain ⟨n, hn, hlt⟩ := hrec N
  exact (lt_asymm (hN n hn) hlt)
