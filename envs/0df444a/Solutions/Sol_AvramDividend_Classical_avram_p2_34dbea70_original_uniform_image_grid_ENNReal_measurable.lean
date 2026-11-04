-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_original_uniform_image_grid_ENNReal_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:53:07.891747+00:00
-- url     : https://prove2.me/submissions/478df191-b46c-4f03-9a25-7f486dfb354b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_measurable_marked_filter_card_ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

/-- The exact actual original negative uniform endpoint-image grid count is measurable. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) (ε : ℝ) :
    Measurable (fun ω : Ω => (((((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)))).filter
      (fun t : ℝ≥0 => X.X t ω -
        X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)).card : ℕ∞) : ℝ≥0∞)) := by
  have hfuture :=
    avram_wave7_01_original_shifted_future_path_coordinate_product_measurable X 0
  have hcoord (t : ℝ≥0) :
      Measurable (fun ω : Ω => X.X t ω - X.X 0 ω) := by
    simpa only [zero_add, Function.comp_def] using (measurable_pi_apply t).comp hfuture
  apply avram_p2_34dbea70_finite_measurable_marked_filter_card_ENNReal
    ((Finset.range (n + 1)).image
      (fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1))))
    (fun t ω => X.X t ω - X.X (t - (T / ((n : ℝ≥0) + 1))) ω < -ε / 2)
  intro t
  have hd : Measurable (fun ω : Ω =>
      X.X t ω - X.X (t - (T / ((n : ℝ≥0) + 1))) ω) := by
    have h := (hcoord t).sub (hcoord (t - (T / ((n : ℝ≥0) + 1))))
    convert h using 1
    funext ω
    dsimp
    ring
  exact measurableSet_Iio.preimage hd
