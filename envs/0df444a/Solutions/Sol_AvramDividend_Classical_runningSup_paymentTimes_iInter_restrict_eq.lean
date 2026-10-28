-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_paymentTimes_iInter_restrict_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:52:55.214235+00:00
-- url     : https://prove2.me/submissions/669e9256-fc45-4617-a5c5-72acbab3797b

import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_runningSup_paymentTimes_iInter_boundary_mass_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (σ : ℕ → ℝ≥0∞) :
    (dividendMeasure (runningSup X) ω).restrict
        (⋂ n, paymentTimes (σ n)) =
      (dividendMeasure (runningSup X) ω).restrict
        (paymentTimes (⨅ n, σ n)) := by
  have hsub : paymentTimes (⨅ n, σ n) ⊆ ⋂ n, paymentTimes (σ n) := by
    intro t ht
    refine mem_iInter.mpr fun n => ⟨ht.1, ht.2.imp id fun h => h.trans_le (iInf_le _ n)⟩
  refine Measure.restrict_congr_set (ae_eq_set.mpr ⟨?_, ?_⟩)
  · exact AvramDividend.Classical.runningSup_paymentTimes_iInter_boundary_mass_zero X ω σ
  · rw [diff_eq_empty.mpr hsub, measure_empty]
