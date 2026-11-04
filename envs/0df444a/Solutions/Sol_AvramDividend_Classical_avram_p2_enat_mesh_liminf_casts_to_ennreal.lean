-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_enat_mesh_liminf_casts_to_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:21:47.295231+00:00
-- url     : https://prove2.me/submissions/79b12088-7c0f-4f91-b420-5ce682de5e53

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The extended-natural liminf of mesh jump counts is preserved
by the continuous order embedding into extended nonnegative reals. -/
theorem solution (a : ℕ → ℕ∞) :
    ((Filter.liminf a Filter.atTop : ℕ∞) : ℝ≥0∞) =
      Filter.liminf (fun n => (a n : ℝ≥0∞)) Filter.atTop := by
  simpa only [Function.comp_def] using
    (ENat.toENNReal_mono.map_liminf_of_continuousAt a
      ENat.continuous_toENNReal.continuousAt)