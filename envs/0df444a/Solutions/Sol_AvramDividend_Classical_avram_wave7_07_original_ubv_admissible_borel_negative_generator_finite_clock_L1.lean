-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_ubv_admissible_borel_negative_generator_finite_clock_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:52:38.4625+00:00
-- url     : https://prove2.me/submissions/09a2ddd5-8362-49e2-a46e-d9e72b79a7e0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_borel_negative_generator_mark_integral_finite_clock_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite-clock source negative-generator Borel mark integrability
from W7-08's UBV extended-cap smoothness and exact admissibility assumptions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : ENNReal.ofReal v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      ∫ z in B, G (p,z) ∂X.ν) μ := by
  classical
  have hv0 : 0 ≤ v := by linarith
  obtain ⟨R, hvR, _, hwR⟩ :=
    avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists w C v hv0 hv hw
  exact avram_wave7_07_original_borel_negative_generator_mark_integral_finite_clock_L1
    X x D hD.1.1 w R u v δ hwR hw_cont hw_neg
    hu hδ hδone huv hvR μ hμ B hBm hBneg
