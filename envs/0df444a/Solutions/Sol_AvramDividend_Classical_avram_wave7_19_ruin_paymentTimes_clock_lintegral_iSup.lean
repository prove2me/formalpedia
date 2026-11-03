-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_ruin_paymentTimes_clock_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:22:18.000218+00:00
-- url     : https://prove2.me/submissions/87c3c5f4-eaf4-4489-bc2c-83533175b303

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_ruin_paymentTimes_clock_iUnion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Pathwise source Stieltjes cash is the monotone limit of integer clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = ⨆ n : ℕ, (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  classical
  let σ : ℝ≥0∞ := ruinTime X x D ω
  let A : ℕ → Set ℝ := fun n =>
    paymentTimes (min σ (n : ℝ≥0∞)) ∩ Iic T
  let Afull : Set ℝ := paymentTimes σ ∩ Iic T
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let μ : Measure ℝ := dividendMeasure D ω
  have hUnion : Afull = ⋃ n : ℕ, A n := by
    simpa only [Afull, A, σ] using
      (avram_wave7_19_ruin_paymentTimes_clock_iUnion X x D ω T)
  have hA (n : ℕ) : MeasurableSet (A n) := by
    dsimp [A, paymentTimes]
    measurability
  have hfull : MeasurableSet Afull := by
    rw [hUnion]
    exact MeasurableSet.iUnion hA
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hm (n : ℕ) : Measurable ((A n).indicator f) :=
    hf.indicator (hA n)
  have hsub (n : ℕ) : A n ⊆ A (n + 1) := by
    intro t ht
    rcases ht with ⟨htPay, htT⟩
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < min σ (n : ℝ≥0∞)) at htPay
    rcases htPay with ⟨ht0, hzero | hlt⟩
    · exact ⟨⟨ht0, Or.inl hzero⟩, htT⟩
    · have hn : (n : ℝ≥0∞) ≤ ((n + 1 : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Nat.le_succ n
      have hmin : min σ (n : ℝ≥0∞) ≤
          min σ ((n + 1 : ℕ) : ℝ≥0∞) := min_le_min_left σ hn
      exact ⟨⟨ht0, Or.inr (lt_of_lt_of_le hlt hmin)⟩, htT⟩
  have hmon : Monotone (fun n : ℕ => (A n).indicator f) := by
    apply monotone_nat_of_le_succ
    intro n
    exact Set.indicator_le_indicator_of_subset (hsub n)
      (fun t => (show (0 : ℝ≥0∞) ≤ f t from zero_le))
  have hpoint (t : ℝ) :
      Afull.indicator f t = ⨆ n : ℕ, (A n).indicator f t := by
    rw [hUnion]
    exact Set.indicator_iUnion_apply (by rfl) A f t
  change (∫⁻ t in Afull, f t ∂μ) =
    ⨆ n : ℕ, (∫⁻ t in A n, f t ∂μ)
  calc
    (∫⁻ t in Afull, f t ∂μ) =
        ∫⁻ t, Afull.indicator f t ∂μ := (lintegral_indicator hfull f).symm
    _ = ∫⁻ t, (⨆ n : ℕ, (A n).indicator f t) ∂μ := by
      apply lintegral_congr
      exact hpoint
    _ = ⨆ n : ℕ, ∫⁻ t, (A n).indicator f t ∂μ :=
      lintegral_iSup hm hmon
    _ = ⨆ n : ℕ, ∫⁻ t in A n, f t ∂μ := by
      apply iSup_congr
      intro n
      exact lintegral_indicator (hA n) f
