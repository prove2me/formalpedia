-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_band_fatou_grid_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:30:46.472198+00:00
-- url     : https://prove2.me/submissions/ca7c4d69-887e-42fb-9a57-57950656367d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_band_mesh_liminf
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_fatou_eventual_grid_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original expected separated jump count is controlled by any established
eventual expectation envelope for its actual negative mesh increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε)
    (M : ℝ≥0∞)
    (hGridMeas : ∀ n : ℕ, Measurable (fun ω : Ω => (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ∞) : ℝ≥0∞)))
    (hGridBound : ∀ᶠ n : ℕ in Filter.atTop,
      (∫⁻ ω, (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ∞) : ℝ≥0∞) ∂P) ≤ M) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)) ∂P) ≤ M := by
  exact avram_p2_a_zero_rate_fatou_eventual_grid_bound P
    (fun ω => ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ Iic (-ε)))
    (fun n ω => (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ∞) : ℝ≥0∞))
    hGridMeas
    (fun ω => avram_p2_a_zero_rate_original_negative_band_mesh_liminf
      X ω T hT ε hε) M hGridBound
