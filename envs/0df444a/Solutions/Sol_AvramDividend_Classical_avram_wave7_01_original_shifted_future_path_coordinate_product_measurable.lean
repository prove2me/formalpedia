-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:27:03.022487+00:00
-- url     : https://prove2.me/submissions/ea6d83f8-4cee-49e8-96f3-19f4c9dd7525

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0) :
    Measurable (fun ω : Ω => fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω) := by
  have hXm : ∀ t, Measurable (X.X t) := fun t =>
    (X.adapted t).mono (𝓕.le t) le_rfl
  exact measurable_pi_lambda _ (fun t => (hXm _).sub (hXm _))
