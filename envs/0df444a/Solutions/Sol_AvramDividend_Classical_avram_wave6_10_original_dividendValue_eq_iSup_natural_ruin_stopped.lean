-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_10_original_dividendValue_eq_iSup_natural_ruin_stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:09:19.640335+00:00
-- url     : https://prove2.me/submissions/d6cd20b3-fcdd-4fce-9adc-2f359c0f0d6f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_paymentTimes_min_ofReal_subset_inter_horizon
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Full original Stieltjes dividend value equals the supremum of exact
    natural ruin-stopped expected rewards, including the time-zero atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D) :
    dividendValue X q x D =
      ⨆ n : ℕ,
        ∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P := by
  apply le_antisymm
  · apply avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
      X q x D hD
    intro n
    exact le_iSup_of_le n le_rfl
  · rw [dividendValue_eq_iSup_truncated X q x D hD]
    refine iSup_le fun n => ?_
    have hsub (ω : Ω) :
        paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ⊆
          paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ) := by
      simpa using (paymentTimes_min_ofReal_subset_inter_horizon
        (ruinTime X x D ω) (n : ℝ) (Nat.cast_nonneg n))
    have hmono (ω : Ω) :
        (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
      MeasureTheory.lintegral_mono_set (hsub ω)
    exact le_iSup_of_le n (MeasureTheory.lintegral_mono hmono)
