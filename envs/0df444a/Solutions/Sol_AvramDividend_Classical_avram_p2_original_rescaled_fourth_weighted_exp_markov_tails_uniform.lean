-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_rescaled_fourth_weighted_exp_markov_tails_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:47:54.868049+00:00
-- url     : https://prove2.me/submissions/71972679-aa7b-4182-b3e1-36cd3cf0a9f4

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_pushforward_upper_tail_linear_smalltime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original source's inverse-time weighted exponential image
has a uniform first-moment Markov tail envelope, for every threshold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ a : ℝ≥0∞,
          a * ((ENNReal.ofReal h)⁻¹ *
            ((P.withDensity (fun ω => ENNReal.ofReal
              ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
              (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
                {z : ℝ | a ≤ ENNReal.ofReal z}) ≤
          ENNReal.ofReal C := by
  obtain ⟨C, hC, hBound⟩ :=
    avram_p2_original_weighted_exp_pushforward_upper_tail_linear_smalltime X
  refine ⟨C, hC, ?_⟩
  filter_upwards [hBound, self_mem_nhdsWithin] with h hh hp a
  have hpos : 0 < h := hp
  have hn : ENNReal.ofReal h ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  have ht : ENNReal.ofReal h ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    a * ((ENNReal.ofReal h)⁻¹ *
        ((P.withDensity (fun ω => ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
            {z : ℝ | a ≤ ENNReal.ofReal z}) =
      (ENNReal.ofReal h)⁻¹ *
        (a * ((P.withDensity (fun ω => ENNReal.ofReal
          ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
          (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))
            {z : ℝ | a ≤ ENNReal.ofReal z}) := by ac_rfl
    _ ≤ (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal (C * h) :=
      by simpa only [mul_comm] using
        (mul_le_mul_left (hh a) (ENNReal.ofReal h)⁻¹)
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
