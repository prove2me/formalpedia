-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian13_actual_masked_random_interval_square_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:30:38.488595+00:00
-- url     : https://prove2.me/submissions/3f1039b6-a155-4247-a885-4428d824c9c9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_predictable_time_section_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical masked Gaussian square energy is integrable between any random
endpoints with finite physical time mass, retaining the original filtration. -/
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
    (μtime : Measure ℝ≥0) (s t : Ω → ℝ≥0)
    (hFinite : ∀ ω, μtime (Ioc (s ω) (t ω)) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∀ ω, IntegrableOn (fun r : ℝ≥0 => (G (r, ω)) ^ 2)
      (Ioc (s ω) (t ω)) μtime := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  obtain ⟨K, hK, hBound⟩ :=
    avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
      X x D hD w a b u v hw1 hau huv hvb
  have hPredictable : Measurable[𝓕.rightCont.predictable] G :=
    (avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
      X x D hD w a b u v hw hau huv hvb μ hμ).1
  have hTimeMeas : ∀ ω, Measurable (fun r : ℝ≥0 => G (r, ω)) :=
    avram_ubv_gaussian10_original_predictable_time_section_measurable
      X G hPredictable
  change ∀ ω, IntegrableOn (fun r : ℝ≥0 => (G (r, ω)) ^ 2)
    (Ioc (s ω) (t ω)) μtime
  intro ω
  apply IntegrableOn.of_bound (hFinite ω)
    (((hTimeMeas ω).pow_const 2).aestronglyMeasurable) (K ^ 2)
  filter_upwards [] with r
  have h0 := abs_nonneg (G (r, ω))
  have h1 := hBound (r, ω)
  have h2 : 0 ≤ K - |G (r, ω)| := sub_nonneg.mpr h1
  have h3 : 0 ≤ K + |G (r, ω)| := add_nonneg hK h0
  have hh := mul_nonneg h2 h3
  simp only [Real.norm_eq_abs, abs_pow]
  nlinarith
