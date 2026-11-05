-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_horizon_discounted_compact_value_predictable_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:57:45.606223+00:00
-- url     : https://prove2.me/submissions/b73fe86c-d6b0-491b-bfb5-ca1c09b0f91d

import Mathlib
import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_predictable_value_compact_L2_from_C2_domain
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- Bounded original predictable discount preserves compact-reserve quadratic energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b u v : ℝ)
    (ha : 0 < a) (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hband : ∀ y : ℝ, y ∈ Ioo a b → ENNReal.ofReal y < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let V : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then w (Y p) else 0
    let weight : ℝ≥0 × Ω → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let J : ℝ≥0 × Ω → ℝ := fun p => weight p * V p
    Measurable[𝓕.rightCont.predictable] J ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((J p) ^ 2) ∂μ) < ⊤ := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let V : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then w (Y p) else 0
  let weight : ℝ≥0 × Ω → ℝ := fun p =>
    if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
  let J : ℝ≥0 × Ω → ℝ := fun p => weight p * V p
  have hV : Measurable[𝓕.rightCont.predictable] V ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((V p)^2) ∂μ) < ⊤ :=
    avram_wave7_18_original_predictable_value_compact_L2_from_C2_domain
      X x D hD C w hw a b u v ha hau huv hvb hband μ hμ
  have hWeight : Measurable[𝓕.rightCont.predictable] weight ∧
      (∀ p, |weight p| ≤ (1 : ℝ)) ∧
      (∀ p, T < p.1 → weight p = 0) :=
    avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
      q hq T
  change Measurable[𝓕.rightCont.predictable] J ∧
    (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((J p)^2) ∂μ) < ⊤
  constructor
  · exact hWeight.1.mul hV.1
  · have hpoint : ∀ p, ENNReal.ofReal ((J p)^2) ≤
        ENNReal.ofReal ((V p)^2) := by
      intro p
      have hwabs := hWeight.2.1 p
      have hwSq : (weight p)^2 ≤ (1 : ℝ) := by
        nlinarith [sq_abs (weight p), abs_nonneg (weight p)]
      have hmul : (weight p)^2 * (V p)^2 ≤ (V p)^2 := by
        calc
          (weight p)^2 * (V p)^2 ≤ 1 * (V p)^2 :=
            mul_le_mul_of_nonneg_right hwSq (sq_nonneg (V p))
          _ = (V p)^2 := one_mul _
      exact ENNReal.ofReal_le_ofReal (by simpa only [J, mul_pow] using hmul)
    exact lt_of_le_of_lt (lintegral_mono hpoint) hV.2
