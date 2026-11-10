-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose17_original_strict_cash_real_monotone_cofinal_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:03:21.387356+00:00
-- url     : https://prove2.me/submissions/c1b8af5a-0e36-4ef7-81aa-3aa3e183bab9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original strictly pre-horizon Stieltjes cash converges along every
increasing cofinal sequence of physical real cutoffs, excluding the endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n) :
    Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by
  let σ : ℝ≥0∞ := ruinTime X x D ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let s : ℕ → Set ℝ := fun n => paymentTimes σ ∩ Iio (u n)
  let e : Set ℝ := paymentTimes σ ∩ Iio T
  let μ : Measure ℝ := (dividendMeasure D ω).withDensity f
  have hPay : MeasurableSet (paymentTimes σ) := by
    unfold paymentTimes
    measurability
  have hsMeas (n : ℕ) : MeasurableSet (s n) :=
    hPay.inter measurableSet_Iio
  have hsMono : Monotone s := by
    intro i j hij t ht
    exact ⟨ht.1, lt_of_lt_of_le ht.2 (hmono hij)⟩
  have hUnion : (⋃ n : ℕ, s n) = e := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
      exact ⟨hn.1, lt_of_lt_of_le hn.2 (hbelow n)⟩
    · intro ht
      obtain ⟨n, hn⟩ := hcover t ht.2
      exact Set.mem_iUnion.mpr ⟨n, ⟨ht.1, hn⟩⟩
  have hMass (n : ℕ) :
      μ (s n) = ∫⁻ t in s n, f t ∂(dividendMeasure D ω) := by
    simpa only [μ] using (withDensity_apply f (hsMeas n))
  have heMass :
      μ e = ∫⁻ t in e, f t ∂(dividendMeasure D ω) := by
    simpa only [μ] using (withDensity_apply f (hPay.inter measurableSet_Iio))
  have hLimit : Tendsto (fun n : ℕ => μ (s n)) atTop (𝓝 (μ e)) := by
    have hAux := tendsto_measure_iUnion_atTop (μ := μ) hsMono
    change Tendsto (fun n : ℕ => μ (s n)) atTop
      (𝓝 (μ (⋃ n : ℕ, s n))) at hAux
    rw [hUnion] at hAux
    exact hAux
  have hDs : IsDividendStrategy 𝓕 D := hD.1.1
  have hClosed :
      (∫⁻ t in paymentTimes σ ∩ Iic T, f t ∂(dividendMeasure D ω)) < ⊤ := by
    have hClosed0 :=
      avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
        D hDs ω σ ⟨T, le_of_lt hT⟩ q hq
    change (∫⁻ t in paymentTimes σ ∩ Iic T, f t ∂(dividendMeasure D ω)) < ⊤ at hClosed0
    exact hClosed0
  have hSub : paymentTimes σ ∩ Iio T ⊆ paymentTimes σ ∩ Iic T := by
    intro t ht
    exact ⟨ht.1, mem_Iic.mpr (le_of_lt (mem_Iio.mp ht.2))⟩
  have hStrict : μ e < ⊤ := by
    rw [heMass]
    exact lt_of_le_of_lt (lintegral_mono_set hSub) hClosed
  have hReal := (ENNReal.tendsto_toReal (ne_of_lt hStrict)).comp hLimit
  change Tendsto (fun n : ℕ => (μ (s n)).toReal) atTop
    (𝓝 ((μ e).toReal)) at hReal
  change Tendsto (fun n : ℕ =>
    (∫⁻ t in s n, f t ∂(dividendMeasure D ω)).toReal)
    atTop (𝓝 ((∫⁻ t in e, f t ∂(dividendMeasure D ω)).toReal))
  simpa only [← hMass, ← heMass] using hReal
