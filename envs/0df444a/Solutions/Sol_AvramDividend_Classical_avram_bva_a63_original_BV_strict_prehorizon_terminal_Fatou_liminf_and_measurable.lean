-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a63_original_BV_strict_prehorizon_terminal_Fatou_liminf_and_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:08:15.630058+00:00
-- url     : https://prove2.me/submissions/3a48a65a-f805-4e60-8628-683f82c14456

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a65_ofReal_liminf_from_real_eventual_lower
import Theorems.Thm_AvramDividend_Classical_avram_bva_a66_original_strict_prehorizon_cash_prepayment_reward_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bva_a68_original_BV_strict_prehorizon_eventual_lower
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
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
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
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
    (T : ℝ) (hT : 0 < T)
    (hInfinite : ¬ X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let r : ℕ → ℝ≥0 := fun n => Real.toNNReal (T - δ n)
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    let G : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (r n : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (r n : ℝ))) * w (riskProcess X x D (r n) ω) else 0))
    (∀ n, Measurable (G n)) ∧
    ∀ n, ∀ᵐ ω ∂P,
      ENNReal.ofReal (F n ω) ≤
        liminf (fun m : ℕ => G m ω) atTop := by
  classical
  intro δ S r F G
  let H : ℕ → Ω → ℝ := fun n ω =>
    ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (r n : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (r n : ℝ))) * w (riskProcess X x D (r n) ω) else 0))
  have hEv := avram_bva_a68_original_BV_strict_prehorizon_eventual_lower
    X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
    x hx hxc D hD hw_nonneg hjump T hT hInfinite
  change ∀ n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in atTop, F n ω - ε < H m ω at hEv
  constructor
  · intro n
    have hMeas :=
      avram_bva_a66_original_strict_prehorizon_cash_prepayment_reward_measurable
        X x C D hD w hw_cont hw_neg q (r n)
    change Measurable (fun ω : Ω => ENNReal.ofReal (H n ω))
    simpa only [H] using hMeas
  · intro n
    filter_upwards [hEv n] with ω hω
    change ENNReal.ofReal (F n ω) ≤
      liminf (fun m : ℕ => ENNReal.ofReal (H m ω)) atTop
    exact avram_bva_a65_ofReal_liminf_from_real_eventual_lower
      (F n ω) (fun m => H m ω) hω
