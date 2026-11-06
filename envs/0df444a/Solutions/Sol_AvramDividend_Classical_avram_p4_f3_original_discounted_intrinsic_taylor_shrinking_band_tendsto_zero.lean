-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_discounted_intrinsic_taylor_shrinking_band_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:00:36.858336+00:00
-- url     : https://prove2.me/submissions/24e11e5f-61b4-4620-82a2-3f59a3ccbfe4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_canonical_shrinking_mark_taylor_energy_upper
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original intensity of the discounted Taylor remainder vanishes with the negative mark cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (f : ℝ → ℝ) (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hf : ContDiffOn ℝ 2 f (Ioo 0 a))
    (T : ℝ≥0) (q : ℝ) (hq : 0 ≤ q) :
    ∃ r : ℝ, 0 < r ∧ r ≤ min l 1 ∧
      (let U : ℝ≥0 × Ω → ℝ := fun p =>
        let y := Function.leftLim
          (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
        if y ∈ Icc l u then y else l
      let A : ℝ≥0 × Ω → ℝ := fun p =>
        if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
      ∀ p : ℝ≥0 × Ω,
        Tendsto (fun n : ℕ =>
          ∫⁻ z in Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
            ENNReal.ofReal (|A p *
              SpectrallyNegativeLevy.generatorIntegrand f (U p) z|)
              ∂X.ν) atTop (𝓝 0)) := by
  classical
  obtain ⟨r, C, hr, hrle, hC, hBound⟩ :=
    avram_p4_f3_original_canonical_shrinking_mark_taylor_energy_upper
      X x D f a l u hl hlu hu hf T q hq
  refine ⟨r, hr, hrle, ?_⟩
  dsimp only
  intro p
  let U : ℝ≥0 × Ω → ℝ := fun p =>
    let y := Function.leftLim
      (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    if y ∈ Icc l u then y else l
  let A : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
  let K : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ z in Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
      ENNReal.ofReal (|A p *
        SpectrallyNegativeLevy.generatorIntegrand f (U p) z|) ∂X.ν
  let Q : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
      ENNReal.ofReal (z ^ 2) ∂X.ν
  have hTail : Tendsto Q atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Q] using
      (avram_p4_h_gaussian_original_nu_quadratic_tail_tendsto_zero X)
  have hCtop : ENNReal.ofReal C ≠ ⊤ :=
    ne_of_lt (ENNReal.ofReal_lt_top : ENNReal.ofReal C < ⊤)
  have hScaled : Tendsto (fun n => ENNReal.ofReal C * Q n)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul hTail (Or.inr hCtop))
  have hCut : ∀ᶠ n : ℕ in atTop,
      1 / ((n : ℝ) + 1) ≤ r := by
    exact ((tendsto_one_div_add_atTop_nhds_zero_nat
      (𝕜 := ℝ)).eventually (Iio_mem_nhds hr)).mono
      (fun n hn => hn.le)
  have hUpper : ∀ᶠ n : ℕ in atTop,
      K n ≤ ENNReal.ofReal C * Q n := by
    filter_upwards [hCut] with n hn
    exact hBound p n hn
  have hLower : ∀ᶠ n : ℕ in atTop,
      (0 : ℝ≥0∞) ≤ K n :=
    Filter.Eventually.of_forall (fun n => bot_le)
  change Tendsto K atTop (𝓝 (0 : ℝ≥0∞))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hScaled hLower hUpper
