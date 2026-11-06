-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_discounted_masked_contact_tail_tendsto_endpoint_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:24:13.227206+00:00
-- url     : https://prove2.me/submissions/efddedda-c08c-4db6-98d8-932c83b22b20

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_masked_contact_tail_intersection_eq_endpoint
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite original stopped discounted cash tails converge exactly to their masked terminal atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        ({(τ : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  let σ : ℝ≥0∞ := ruinTime X x D ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let s : ℕ → Set ℝ := fun n =>
    paymentTimes σ ∩ Ioc ((τ : ℝ) - δ n) (τ : ℝ)
  let e : Set ℝ := paymentTimes σ ∩ ({(τ : ℝ)} : Set ℝ)
  let μ : Measure ℝ := (dividendMeasure D ω).withDensity f
  have hPay : MeasurableSet (paymentTimes σ) := by
    unfold paymentTimes
    measurability
  have hsMeas (n : ℕ) : MeasurableSet (s n) :=
    hPay.inter measurableSet_Ioc
  have hsMono : Antitone s := by
    intro i j hij t ht
    change t ∈ paymentTimes σ ∩
      Ioc ((τ : ℝ) - δ j) (τ : ℝ) at ht
    change t ∈ paymentTimes σ ∩
      Ioc ((τ : ℝ) - δ i) (τ : ℝ)
    exact ⟨ht.1, ⟨by linarith [hδanti hij, ht.2.1], ht.2.2⟩⟩
  have hInter : (⋂ n : ℕ, s n) = e := by
    simpa only [s, e, σ] using
      (avram_p3_grid4_original_masked_contact_tail_intersection_eq_endpoint
        X x D ω τ δ hδpos hδ)
  have hTReal : (τ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hτT
  have hsSub : s 0 ⊆ paymentTimes σ ∩ Iic (T : ℝ) := by
    intro t ht
    exact ⟨ht.1, le_trans ht.2.2 hTReal⟩
  have hMass (n : ℕ) :
      μ (s n) = ∫⁻ t in s n, f t ∂(dividendMeasure D ω) := by
    simpa only [μ] using (withDensity_apply f (hsMeas n))
  have heMass :
      μ e = ∫⁻ t in e, f t ∂(dividendMeasure D ω) := by
    simpa only [μ] using
      (withDensity_apply f (hPay.inter (measurableSet_singleton (τ : ℝ))))
  have hFinite : μ (s 0) < ⊤ := by
    rw [hMass 0]
    have hBound :=
      avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
        D hD ω σ T q hq
    exact lt_of_le_of_lt (lintegral_mono_set hsSub) (by simpa only [f] using hBound)
  have hLimit : Tendsto (fun n : ℕ => μ (s n)) atTop (𝓝 (μ e)) := by
    have hAux :=
      tendsto_measure_iInter_atTop
        (fun n => (hsMeas n).nullMeasurableSet)
        hsMono ⟨0, ne_of_lt hFinite⟩
    change Tendsto (fun n : ℕ => μ (s n)) atTop
      (𝓝 (μ (⋂ n : ℕ, s n))) at hAux
    rw [hInter] at hAux
    exact hAux
  change Tendsto (fun n : ℕ => ∫⁻ t in s n, f t ∂(dividendMeasure D ω))
    atTop (𝓝 (∫⁻ t in e, f t ∂(dividendMeasure D ω)))
  rw [← heMass]
  simpa only [← hMass] using hLimit
