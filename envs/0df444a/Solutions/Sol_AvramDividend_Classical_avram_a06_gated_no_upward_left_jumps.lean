-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_gated_no_upward_left_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T23:46:23.749652+00:00
-- url     : https://prove2.me/submissions/de95b547-f73b-46ce-af50-202d60174a10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Replacing exceptional paths by zero cannot create upward jumps. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ) (G : Set Ω)
    [DecidablePred (fun ω => ω ∈ G)]
    (hdown : ∀ ω ∈ G, ∀ (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 => X s ω) (nhdsWithin t (Iio t)) (nhds l) →
      X t ω ≤ l) :
    ∀ (ω : Ω) (t : ℝ≥0) (l : ℝ), 0 < t →
      Tendsto (fun s : ℝ≥0 => if ω ∈ G then X s ω else 0)
        (nhdsWithin t (Iio t)) (nhds l) →
      (if ω ∈ G then X t ω else 0) ≤ l := by
  intro ω t l ht hl
  by_cases hw : ω ∈ G
  · have hsource : Tendsto (fun s : ℝ≥0 => X s ω)
        (nhdsWithin t (Iio t)) (nhds l) := by
      simpa [hw] using hl
    simpa [hw] using hdown ω hw t l ht hsource
  · haveI : (𝓝[<] t).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
    have hl0 : Tendsto (fun _ : ℝ≥0 => (0 : ℝ))
        (𝓝[<] t) (nhds l) := by
      simpa [hw] using hl
    have hconst : Tendsto (fun _ : ℝ≥0 => (0 : ℝ))
        (𝓝[<] t) (nhds (0 : ℝ)) := tendsto_const_nhds
    have heq : (0 : ℝ) = l := tendsto_nhds_unique hconst hl0
    simpa [hw] using heq.le
