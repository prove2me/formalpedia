-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_rescaled_weighted_polynomial_moment_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:20:50.179893+00:00
-- url     : https://prove2.me/submissions/96b713fa-b28c-4906-98a9-9cb46cab8640

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every original rescaled weighted exponential polynomial moment,
including arbitrarily high degrees for uniform integrability, is
uniformly bounded on a punctured interval near time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        (ENNReal.ofReal h)⁻¹ *
          (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
            ((P.withDensity (fun ω => ENNReal.ofReal
              ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
              (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))) ≤
          ENNReal.ofReal C := by
  obtain ⟨C, hC, hBound⟩ :=
    avram_p2_original_weighted_exp_pushforward_moments_linear_smalltime_bound X k
  refine ⟨C, hC, ?_⟩
  filter_upwards [hBound, self_mem_nhdsWithin] with h hh hp
  have hpos : 0 < h := hp
  have hn : ENNReal.ofReal h ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hpos)
  have ht : ENNReal.ofReal h ≠ ⊤ := ENNReal.ofReal_ne_top
  calc
    (ENNReal.ofReal h)⁻¹ *
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))) ≤
      (ENNReal.ofReal h)⁻¹ * ENNReal.ofReal (C * h) :=
        by simpa only [mul_comm] using
          (mul_le_mul_left hh (ENNReal.ofReal h)⁻¹)
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
