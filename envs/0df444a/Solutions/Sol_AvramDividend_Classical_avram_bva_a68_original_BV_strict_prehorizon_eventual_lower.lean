-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a68_original_BV_strict_prehorizon_eventual_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:16:37.413105+00:00
-- url     : https://prove2.me/submissions/d88f18d9-da72-411a-8801-0b8cc1df01fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a67_original_strict_positive_uniform_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_killed_terminal_left_grid_lower_bound_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_strict_discounted_cash_toReal_mono
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
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
    let G : ℕ → Ω → ℝ := fun n ω =>
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (r n : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (r n : ℝ))) * w (riskProcess X x D (r n) ω) else 0))
    ∀ n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ m in atTop, F n ω - ε < G m ω := by
  classical
  intro δ S r F G
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hSpos : 0 < S := by exact_mod_cast hT
  have hClock : Tendsto r atTop (𝓝[<] S) := by
    simpa only [r, δ, S] using
      (avram_bva_a67_original_strict_positive_uniform_clock_tendsto T hT)
  have hTerm := avram_p3_bv_original_killed_terminal_left_grid_lower_bound_ae
    X D hDiv x w hw_cont q hw_nonneg S hSpos r hClock
  have hTcast : (S : ℝ) = T := rfl
  have hFinite (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
    simpa only [hTcast] using
      (avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
        D hDiv ω (ruinTime X x D ω) S q hq.le)
  have hClockReal (m : ℕ) : (r m : ℝ) =
      T - T / ((m : ℝ) + 2) := by
    have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm : (1 : ℝ) < ((m : ℝ) + 2) := by linarith
    have hpos : 0 < T - T / ((m : ℝ) + 2) :=
      sub_pos.mpr (div_lt_self hT hm)
    simpa only [r, δ] using
      (Real.coe_toNNReal (T - T / ((m : ℝ) + 2)) (le_of_lt hpos))
  intro n
  filter_upwards [hTerm] with ω hω
  intro ε hε
  filter_upwards [hω ε hε, Filter.eventually_ge_atTop n] with m hTm hnm
  have hCash := avram_bvb45_original_strict_discounted_cash_toReal_mono
    T hT q (ruinTime X x D ω) (dividendMeasure D ω)
    (hFinite ω) n m hnm
  have hCashBound :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r m : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
    simpa only [δ, hClockReal] using hCash
  change
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0) - ε <
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (r m : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (r m : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (r m : ℝ))) * w (riskProcess X x D (r m) ω) else 0)
  rw [hTcast] at hTm
  linarith [hCashBound, hTm]
