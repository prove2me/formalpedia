-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_rescaled_fourth_weighted_source_mass_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:47:51.413235+00:00
-- url     : https://prove2.me/submissions/52259cdf-abe5-488b-a433-06e30081d090

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original fourth-weighted source mass, rescaled by inverse time,
is uniformly finite near zero. This supplies the zeroth-moment tightness
bound for the actual original-source exponential image. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (ENNReal.ofReal h)⁻¹ *
          (∫⁻ ω, ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC, hBound⟩ :=
    avram_p2_original_tilted_weighted_ennreal_linear_smalltime_bound X 0 le_rfl
  refine ⟨C, hC, ?_⟩
  filter_upwards [hBound, self_mem_nhdsWithin] with h hh hp
  have hpos : 0 < h := hp
  have hn : ENNReal.ofReal h ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  have ht : ENNReal.ofReal h ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsmall :
      (∫⁻ ω, ENNReal.ofReal
        ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P) ≤
      ENNReal.ofReal (C * h) := by
    simpa only [zero_mul, Real.exp_zero, one_mul] using hh
  calc
    (ENNReal.ofReal h)⁻¹ *
        (∫⁻ ω, ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4) ∂P) ≤
      (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal (C * h) :=
        by simpa only [mul_comm] using
          (mul_le_mul_left hsmall (ENNReal.ofReal h)⁻¹)
    _ = (ENNReal.ofReal h)⁻¹ *
          (ENNReal.ofReal C * ENNReal.ofReal h) := by
        rw [ENNReal.ofReal_mul (le_of_lt hC)]
    _ = ENNReal.ofReal C := by
      calc
        (ENNReal.ofReal h)⁻¹ *
            (ENNReal.ofReal C * ENNReal.ofReal h) =
          ((ENNReal.ofReal h)⁻¹ * ENNReal.ofReal h) *
            ENNReal.ofReal C := by ac_rfl
        _ = ENNReal.ofReal C := by
          rw [ENNReal.inv_mul_cancel hn ht, one_mul]
