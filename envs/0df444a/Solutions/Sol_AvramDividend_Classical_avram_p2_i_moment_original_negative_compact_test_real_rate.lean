-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_original_negative_compact_test_real_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:22:54.048223+00:00
-- url     : https://prove2.me/submissions/2031b681-17d0-44e1-8adb-a50c348a28db

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_original_negative_compact_test_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original compact-negative source rate uses the standard real inverse time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f) (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0) :
    Tendsto (fun h : ℝ => if 0 < h then
      h⁻¹ * (∫ ω, f (X.X (Real.toNNReal h) ω) ∂P)
      else 0)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by
  have hbase := avram_p2_i_moment_original_negative_compact_test_rate
    X f hf a ε hε hflower hfupper
  have hfun :
      (fun h : ℝ => if 0 < h then
        ((ENNReal.ofReal h)⁻¹).toReal *
          (∫ ω, f (X.X (Real.toNNReal h) ω) ∂P)
        else 0) =
      (fun h : ℝ => if 0 < h then
        h⁻¹ * (∫ ω, f (X.X (Real.toNNReal h) ω) ∂P)
        else 0) := by
    funext h
    by_cases hh : 0 < h
    · simp only [if_pos hh]
      rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hh.le]
    · simp [hh]
  rw [hfun] at hbase
  exact hbase
