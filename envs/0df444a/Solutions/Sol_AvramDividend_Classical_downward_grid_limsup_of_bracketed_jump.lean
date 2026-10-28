-- Prove2me | solution 1 for AvramDividend.Classical.downward_grid_limsup_of_bracketed_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:13:34.416829+00:00
-- url     : https://prove2.me/submissions/4bd6f963-f811-4000-84a3-a9c7857ac833

import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set
open scoped NNReal

/-- Converging grid brackets detect every strictly downward jump in the
countable path event at arbitrarily fine observation resolutions. -/
theorem solution
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0))
    (s u : ℕ → ℝ≥0) (f : ℝ≥0 → ℝ)
    (t : ℝ≥0) (left a : ℝ)
    (hgrid : ∀ n, (s n, u n) ∈ grid n)
    (hs : Tendsto (fun n => f (s n)) atTop (nhds left))
    (hu : Tendsto (fun n => f (u n)) atTop (nhds (f t)))
    (hjump : f t - left < -a) :
    f ∈ (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
      ⋃ ij ∈ grid n.1,
        {g : ℝ≥0 → ℝ | g ij.2 - g ij.1 < -a}) := by
  have hlim : Tendsto (fun n : ℕ => f (u n) - f (s n))
      atTop (nhds (f t - left)) := hu.sub hs
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (hlim.eventually (Iio_mem_nhds hjump))
  simp only [Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq]
  intro N
  let k : ℕ := max N M
  refine ⟨⟨k, le_max_left N M⟩, (s k, u k), hgrid k, ?_⟩
  exact hM k (le_max_right N M)
