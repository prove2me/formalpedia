-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_negative_borel_mark_canonical_cutoff_exhaustion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:06:55.682206+00:00
-- url     : https://prove2.me/submissions/e2fcc4b8-a142-4c34-bf3d-b95cbce3382e

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_harmonic_negative_band_exhaustion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    (B : Set ℝ) (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    ∃ C : ℕ → Set ℝ,
      (∀ n, MeasurableSet (C n)) ∧
      Monotone C ∧
      (⋃ n, C n) = B ∧
      (∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε)) := by
  rcases avram_p2_c_borel_harmonic_negative_band_exhaustion B hB hNeg with
    ⟨hMeas, hMonotone, hCover, hCutoff⟩
  exact ⟨fun n => B ∩ Iic (-(1 / ((n : ℝ) + 1))),
    hMeas, hMonotone, hCover, hCutoff⟩
