-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva35_original_BV_strict_inner_cash_terminal_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:54:41.085364+00:00
-- url     : https://prove2.me/submissions/6560f914-2cf9-4c50-b2f1-9d301c36128b

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_strict_discounted_cash_real_monotone
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
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
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ n m : ℕ, n ≤ m → ∀ ω, F n ω ≤ F m ω := by
  intro δ S F n m hnm ω
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have horder : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by
    exact_mod_cast Nat.add_le_add_right hnm 2
  have hδ : δ m ≤ δ n := by
    dsimp [δ]
    apply (div_le_div_iff₀ hm2 hn2).2
    nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr horder)]
  have htime : T - δ n ≤ T - δ m := by linarith
  have hbase : T - δ n ≥ 0 := by
    have hden : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith
    have hdiv : δ n ≤ T := by
      dsimp [δ]
      apply (div_le_iff₀ hn2).2
      nlinarith [mul_nonneg (le_of_lt hT) (sub_nonneg.mpr hden)]
    linarith
  have hCash :=
    avram_p3_grid3_original_strict_discounted_cash_real_monotone
      X q (le_of_lt hq) x D hD.1.1 ω
      (T - δ n) (T - δ m) hbase htime
  change
    (∫⁻ r in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) ≤
    (∫⁻ r in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ m),
      ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  simpa only [add_le_add_iff_right] using hCash
