-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_cofinal_random_clocks_full_cash_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:21:36.814486+00:00
-- url     : https://prove2.me/submissions/126d8a72-089a-4f83-8fdf-69a1938650cb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_cofinal_random_clocks_paymentTimes_iUnion
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Source Stieltjes cash on the original paying set is the monotone clock limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) (hσ : Monotone σ)
    (hSup : (⨆ k : ℕ, σ k) = ruinTime X x D ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      ⨆ k : ℕ, (∫⁻ t in paymentTimes (σ k) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  classical
  let A : ℕ → Set ℝ := fun k => paymentTimes (σ k) ∩ Iic T
  let U : Set ℝ := ⋃ k : ℕ, A k
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let μ : Measure ℝ := dividendMeasure D ω
  have hUnion : paymentTimes (ruinTime X x D ω) ∩ Iic T = U := by
    simpa only [U, A] using
      (avram_wave7_19_original_ruin_cofinal_random_clocks_paymentTimes_iUnion
        X x D ω T σ hSup)
  have hA (k : ℕ) : MeasurableSet (A k) := by
    dsimp [A, paymentTimes]; measurability
  have hU : MeasurableSet U := MeasurableSet.iUnion hA
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hsub (k : ℕ) : A k ⊆ A (k + 1) := by
    intro t ht
    refine ⟨?_, ht.2⟩
    have hp := ht.1
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ k) at hp
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ (k + 1))
    rcases hp.2 with hz | hlt
    · exact ⟨hp.1, Or.inl hz⟩
    · exact ⟨hp.1, Or.inr (lt_of_lt_of_le hlt (hσ (Nat.le_succ k)))⟩
  have hm (k : ℕ) : Measurable ((A k).indicator f) := hf.indicator (hA k)
  have hmon : Monotone (fun k : ℕ => (A k).indicator f) := by
    apply monotone_nat_of_le_succ
    intro k
    exact Set.indicator_le_indicator_of_subset (hsub k)
      (fun t => (show (0 : ℝ≥0∞) ≤ f t from zero_le))
  have hpoint (t : ℝ) : U.indicator f t = ⨆ k : ℕ, (A k).indicator f t := by
    change (⋃ k : ℕ, A k).indicator f t = _
    exact Set.indicator_iUnion_apply (by rfl) A f t
  change (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T, f t ∂μ) =
    ⨆ k : ℕ, (∫⁻ t in A k, f t ∂μ)
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T, f t ∂μ) =
        ∫⁻ t in U, f t ∂μ := by rw [hUnion]
    _ = ∫⁻ t, U.indicator f t ∂μ :=
      (lintegral_indicator hU f).symm
    _ = ∫⁻ t, (⨆ k : ℕ, (A k).indicator f t) ∂μ := by
      apply lintegral_congr; exact hpoint
    _ = ⨆ k : ℕ, ∫⁻ t, (A k).indicator f t ∂μ :=
      lintegral_iSup hm hmon
    _ = ⨆ k : ℕ, ∫⁻ t in A k, f t ∂μ := by
      apply iSup_congr
      intro k
      exact lintegral_indicator (hA k) f
