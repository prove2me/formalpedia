-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_strict_masked_contact_tail_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:39:00.537077+00:00
-- url     : https://prove2.me/submissions/a25e9f04-6bcc-4b51-a919-d80f1814cb91

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

/-- Discounted strictly left-contact cash tails vanish; the right endpoint atom is excluded. -/
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
        Ioo ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (𝓝 0) := by
  let σ : ℝ≥0∞ := ruinTime X x D ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let s : ℕ → Set ℝ := fun n =>
    paymentTimes σ ∩ Ioo ((τ : ℝ) - δ n) (τ : ℝ)
  let μ : Measure ℝ := (dividendMeasure D ω).withDensity f
  have hPay : MeasurableSet (paymentTimes σ) := by
    unfold paymentTimes
    measurability
  have hsMeas (n : ℕ) : MeasurableSet (s n) :=
    hPay.inter measurableSet_Ioo
  have hsMono : Antitone s := by
    intro i j hij t ht
    change t ∈ paymentTimes σ ∩
      Ioo ((τ : ℝ) - δ j) (τ : ℝ) at ht
    change t ∈ paymentTimes σ ∩
      Ioo ((τ : ℝ) - δ i) (τ : ℝ)
    exact ⟨ht.1, ⟨by linarith [hδanti hij, ht.2.1], ht.2.2⟩⟩
  have hInter : (⋂ n : ℕ, s n) = ∅ := by
    ext t
    constructor
    · intro ht
      have hMem : t ∈ paymentTimes σ ∩ ({(τ : ℝ)} : Set ℝ) := by
        rw [← (avram_p3_grid4_original_masked_contact_tail_intersection_eq_endpoint
          X x D ω τ δ hδpos hδ)]
        refine Set.mem_iInter.mpr ?_
        intro n
        have hn := Set.mem_iInter.mp ht n
        exact ⟨hn.1, ⟨hn.2.1, le_of_lt hn.2.2⟩⟩
      have hlt : t < (τ : ℝ) := (Set.mem_iInter.mp ht 0).2.2
      have heq : t = (τ : ℝ) := by simpa using hMem.2
      exact lt_irrefl _ (heq ▸ hlt)
    · intro ht
      simp at ht
  have hTReal : (τ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hτT
  have hsSub : s 0 ⊆ paymentTimes σ ∩ Iic (T : ℝ) := by
    intro t ht
    exact ⟨ht.1, le_trans (le_of_lt ht.2.2) hTReal⟩
  have hMass (n : ℕ) :
      μ (s n) = ∫⁻ t in s n, f t ∂(dividendMeasure D ω) := by
    simpa only [μ] using (withDensity_apply f (hsMeas n))
  have hFinite : μ (s 0) < ⊤ := by
    rw [hMass 0]
    have hBound :=
      avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
        D hD ω σ T q hq
    exact lt_of_le_of_lt (lintegral_mono_set hsSub) (by simpa only [f] using hBound)
  have hLimit : Tendsto (fun n : ℕ => μ (s n)) atTop (𝓝 0) := by
    have hAux :=
      tendsto_measure_iInter_atTop
        (fun n => (hsMeas n).nullMeasurableSet)
        hsMono ⟨0, ne_of_lt hFinite⟩
    change Tendsto (fun n : ℕ => μ (s n)) atTop
      (𝓝 (μ (⋂ n : ℕ, s n))) at hAux
    rw [hInter, measure_empty] at hAux
    exact hAux
  change Tendsto (fun n : ℕ => ∫⁻ t in s n, f t ∂(dividendMeasure D ω))
    atTop (𝓝 0)
  simpa only [← hMass] using hLimit
