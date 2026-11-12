-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_positive_shift_actual_generator_time_recombination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:23:34.675607+00:00
-- url     : https://prove2.me/submissions/8b18bed0-2efd-4ef0-8153-641ff9279bd5

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_sweep9_original_controlled_prestate_ambient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
import Theorems.Thm_AvramDividend_Classical_avram_chat24_bv_compact_discounted_time_generator_recombination
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_genint : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hTop : C = ⊤) (δ : ℝ) (hδ : 0 < δ) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let a : ℝ := min δ 1 / 2
    let b : ℝ := x + δ + T * X.drift + 1
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => (x + δ) + X.X s p.2 - rightLimit D s p.2) p.1
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) ∧
          Y p.1 ∈ Icc a b ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1)) else 0
    let μ : Measure ℝ≥0 :=
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∀ᵐ ω ∂P,
      (∫ t, if (t : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) *
          (X.drift * deriv w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ) =
      -(∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂μ) +
      (∫ t, if (t : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) ∧ Y (t, ω) ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) *
          (X.generator w (Y (t, ω)) - q * w (Y (t, ω))) else 0 ∂μ) := by
  classical
  intro S a b τ Y NX H μ
  have hd : 0 < X.drift :=
    (avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
      X hX hBV).1
  have ha : 0 < a := by dsimp [a]; positivity
  have ha2 : a ≤ 2 := by dsimp [a]; linarith [min_le_right δ (1 : ℝ)]
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith [min_le_left δ (1 : ℝ), mul_nonneg hT hd.le]
  have hs : ContDiffOn ℝ 1 w (Ioi 0) :=
    hw_smooth.mono fun y hy => ⟨hy, by simp [hTop]⟩
  have hYm : Measurable Y :=
    avram_integration_sweep9_original_controlled_prestate_ambient_measurable X (x + δ) D hD.1.1
  letI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  filter_upwards [] with ω
  have hp := avram_chat24_bv_compact_discounted_time_generator_recombination
    X hBV w hw_cont hw_neg hs q a b hq.le ha ha2 hab
    (fun y hy => hw_genint y (ha.trans_le hy.1) (by simp [hTop]))
    μ (fun t => Y (t, ω)) (hYm.comp (measurable_id.prodMk measurable_const)) (τ ω)
  simpa only [H, ENNReal.coe_le_coe] using hp
