-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_actual_discounted_stopped_Taylor_rightcont_physical_product_L1_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:00:20.858363+00:00
-- url     : https://prove2.me/submissions/fb6495e0-c373-4a2f-baac-d2842b13ef35

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L1_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
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
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ),
        ENNReal.ofReal (|GW p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) < ⊤) := by
  classical
  intro Y H HS a GW
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  obtain ⟨_, habs, _⟩ :=
    avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
      (𝓕 := 𝓕) q hq T
  have hBound : ∀ p : ((ℝ≥0 × Ω) × ℝ), |GW p| ≤ |HS p| := by
    intro p
    change |a p.1 * HS p| ≤ |HS p|
    rw [abs_mul]
    calc
      |a p.1| * |HS p| ≤ 1 * |HS p| :=
        mul_le_mul_of_nonneg_right (habs p.1) (abs_nonneg _)
      _ = |HS p| := one_mul _
  have hIntegral :
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ), ENNReal.ofReal (|GW p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) ≤
      (∫⁻ p : ((ℝ≥0 × Ω) × ℝ), ENNReal.ofReal (|HS p|)
        ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ))))) :=
    lintegral_mono (fun p => ENNReal.ofReal_le_ofReal (hBound p))
  exact lt_of_le_of_lt hIntegral
    (avram_wave6_02_actual_stopped_C2_taylor_rightcont_physical_product_L1_energy
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ)
