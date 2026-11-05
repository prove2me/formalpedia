-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_public_original_mark_rate_band_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:51:32.450527+00:00
-- url     : https://prove2.me/submissions/71ad10c4-82fe-4ef8-95c9-8fda2c530932

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_intrinsic_intensity_measure_complete
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every bounded real test supported on a separated negative band is integrable against the original intrinsic mark rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ)
    (hbound : ∀ y : ℝ,
      ‖f y‖ ≤ (Iic (-ε)).indicator (fun _ : ℝ => C) y) :
    ∃ markRate : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * markRate B) ∧
      Integrable f markRate := by
  obtain ⟨markRate, hRate, hFinite, _, _⟩ :=
    avram_p2_c_borel_original_intrinsic_intensity_measure_complete X
  have hBand : markRate (Iic (-ε)) < ⊤ := hFinite ε hε
  have hOn : IntegrableOn (fun _ : ℝ => C) (Iic (-ε)) markRate :=
    integrableOn_const (ne_of_lt hBand) (by finiteness)
  have hBase : Integrable ((Iic (-ε)).indicator (fun _ : ℝ => C)) markRate :=
    hOn.integrable_indicator measurableSet_Iic
  refine ⟨markRate, hRate, ?_⟩
  exact hBase.mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
