-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_stopped_C2_taylor_rightcont_L2_centered_band_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:35:16.83631+00:00
-- url     : https://prove2.me/submissions/c8ade56e-dd9d-4cf1-928a-938f3817c90a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_real_product_L2_square_to_eNorm_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      ∀ (B : ℕ → Set (((ℝ≥0 × Ω) × ℝ)))
        (hB : ∀ n, MeasurableSet (B n))
        (hBfinite : ∀ n, (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) (B n) < ⊤)
        (hBmono : Monotone B)
        (hBcover : (⋃ n, B n) = Set.univ)
        (M : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
        (hfinite_band_isometry_bound : ∀ m n, m ≤ n →
          dist (M m) (M n) ≤
            (eLpNorm ((B m)ᶜ.indicator HS) (2 : ℝ≥0∞)
              (μ.prod (X.ν.restrict (Iio (0 : ℝ))))).toReal)
        (hcentered : ∀ n, ∫ ω, (M n) ω ∂P = 0),
      ∃ Mlimit : Lp ℝ (2 : ℝ≥0∞) P,
        Tendsto M Filter.atTop (nhds Mlimit) ∧
        (∫ ω, Mlimit ω ∂P) = 0) := by
  classical
  intro Y H HS
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  intro B hB hBfinite hBmono hBcover M hfinite_band_isometry_bound hcentered
  obtain ⟨hHSm, _, _⟩ :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ
  have hSquare :=
    avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L2_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ
  have hEnergy : (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
      ‖HS p‖ₑ ^ (2 : ℝ) ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤ :=
    avram_wave6_02_real_product_L2_square_to_eNorm_energy
      (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) HS hSquare
  exact avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero
    P (μ.prod (X.ν.restrict (Iio (0 : ℝ)))) HS hHSm hEnergy
    B hB hBfinite hBmono hBcover M hfinite_band_isometry_bound hcentered
