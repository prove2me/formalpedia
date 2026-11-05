-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_e_compensator_measurable_eventual_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:03:36.918929+00:00
-- url     : https://prove2.me/submissions/93c217d5-c1fb-4da8-9d8d-949a8c313151

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped ENNReal

/-- Eventual equality to measurable source grid counts makes the exact pair limit measurable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (G : ℕ → Ω → ℝ≥0∞) (K : Ω → ℝ≥0∞)
    (hMeas : ∀ n, Measurable (G n))
    (hEventual : ∀ ω, ∀ᶠ n in atTop, G n ω = K ω) :
    Measurable K := by
  have hlim (ω : Ω) :
      Filter.liminf (fun n : ℕ => G n ω) atTop = K ω := by
    calc
      Filter.liminf (fun n : ℕ => G n ω) atTop =
          Filter.liminf (fun _ : ℕ => K ω) atTop :=
        Filter.liminf_congr (hEventual ω)
      _ = K ω := Filter.liminf_const _
  have hMeasLim : Measurable
      (fun ω => Filter.liminf (fun n : ℕ => G n ω) atTop) :=
    Measurable.liminf hMeas
  have hEq : (fun ω => Filter.liminf (fun n : ℕ => G n ω) atTop) = K := by
    funext ω
    exact hlim ω
  rw [← hEq]
  exact hMeasLim
