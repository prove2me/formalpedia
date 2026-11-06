-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_grid4_original_strict_real_cash_prefix_direct_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:20:20.775216+00:00
-- url     : https://prove2.me/submissions/53b7624b-6ba8-4062-bbed-35545534695b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Direct real strict-prefix convergence with finite genuine Stieltjes mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T) (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n) (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)
      atTop
      (𝓝 ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal)) := by
  let σ : ℝ≥0∞ := ruinTime X x D ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let s : ℕ → Set ℝ := fun n => paymentTimes σ ∩ Iio (T - δ n)
  let e : Set ℝ := paymentTimes σ ∩ Iio T
  let μ : Measure ℝ := (dividendMeasure D ω).withDensity f
  have hPay : MeasurableSet (paymentTimes σ) := by
    unfold paymentTimes
    measurability
  have hsMeas (n : ℕ) : MeasurableSet (s n) := hPay.inter measurableSet_Iio
  have hsMono : Monotone s := by
    intro i j hij t ht
    change t ∈ paymentTimes σ ∩ Iio (T - δ i) at ht
    change t ∈ paymentTimes σ ∩ Iio (T - δ j)
    exact ⟨ht.1, show t < T - δ j by
      have htlt : t < T - δ i := ht.2
      linarith [htlt, hδanti hij]⟩
  have hUnion : (⋃ n : ℕ, s n) = e := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
      have hlt : t < T - δ n := hn.2
      exact ⟨hn.1, lt_trans hlt (sub_lt_self T (hδpos n))⟩
    · intro ht
      have hlt : t < T := ht.2
      have hOpen : Iio (T - t) ∈ 𝓝 (0 : ℝ) :=
        isOpen_Iio.mem_nhds (by simpa only [mem_Iio] using (sub_pos.mpr hlt))
      have hEv : ∀ᶠ n in atTop, δ n < T - t :=
        hδ.eventually hOpen
      obtain ⟨n, hn⟩ := hEv.exists
      exact Set.mem_iUnion.mpr ⟨n, ⟨ht.1, show t < T - δ n by linarith [hn]⟩⟩
  have hMass (n : ℕ) : μ (s n) = ∫⁻ t in s n, f t ∂(dividendMeasure D ω) := by
    simpa only [μ] using (withDensity_apply f (hsMeas n))
  have heMass : μ e = ∫⁻ t in e, f t ∂(dividendMeasure D ω) := by
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
    intro t ht; exact ⟨ht.1, mem_Iic.mpr (le_of_lt (mem_Iio.mp ht.2))⟩
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
