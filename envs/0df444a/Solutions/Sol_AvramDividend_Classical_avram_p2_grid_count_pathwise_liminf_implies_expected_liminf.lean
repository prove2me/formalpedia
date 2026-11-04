-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_grid_count_pathwise_liminf_implies_expected_liminf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:21:43.673086+00:00
-- url     : https://prove2.me/submissions/a21ccef8-8ec2-4733-8fdf-35306caa7cd4

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.LiminfLimsup
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Fatou transfers a samplewise lower bound by the grid-count liminf
to an upper bound on the expected intrinsic count. This does not assume
a Lévy jump intensity, a compensator or a Poisson representation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (jumpCount : Ω → ℝ≥0∞) (grid : ℕ → Ω → ℝ≥0∞)
    (hgrid : ∀ n, Measurable (grid n))
    (hBound : ∀ ω, jumpCount ω ≤
      Filter.liminf (fun n => grid n ω) Filter.atTop) :
    (∫⁻ ω, jumpCount ω ∂P) ≤
      Filter.liminf (fun n => ∫⁻ ω, grid n ω ∂P) Filter.atTop := by
  calc
    (∫⁻ ω, jumpCount ω ∂P) ≤
        ∫⁻ ω, Filter.liminf (fun n => grid n ω) Filter.atTop ∂P :=
      lintegral_mono hBound
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, grid n ω ∂P) Filter.atTop :=
      lintegral_liminf_le hgrid