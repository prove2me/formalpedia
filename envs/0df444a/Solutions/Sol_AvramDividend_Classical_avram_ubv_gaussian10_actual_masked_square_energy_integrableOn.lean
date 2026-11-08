-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:46:09.877196+00:00
-- url     : https://prove2.me/submissions/52a75c95-8183-4782-bd44-cacd890022a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_predictable_time_section_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_uniform_source_square_energy_integrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True Gaussian gradient coefficient has all-path finite-horizon square energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∀ ω, IntegrableOn (fun t : ℝ≥0 => (G (t, ω)) ^ 2)
      (Ioc (0 : ℝ≥0) T) μtime := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  obtain ⟨C, hC, hBound⟩ :=
    avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
      X x D hD w a b u v hw1 hau huv hvb
  have hPredictable : Measurable[𝓕.rightCont.predictable] G :=
    (avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
      X x D hD w a b u v hw hau huv hvb μ hμ).1
  have hTimeMeas : ∀ ω, Measurable (fun t : ℝ≥0 => G (t, ω)) :=
    avram_ubv_gaussian10_original_predictable_time_section_measurable
      X G hPredictable
  change ∀ ω, IntegrableOn (fun t : ℝ≥0 => (G (t, ω)) ^ 2)
    (Ioc (0 : ℝ≥0) T) μtime
  exact avram_ubv_gaussian10_uniform_source_square_energy_integrableOn
    G hTimeMeas μtime T hFinite C hC hBound
