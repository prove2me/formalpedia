-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_band_eligible_zero_drop_atomless
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:21:12.016901+00:00
-- url     : https://prove2.me/submissions/e14a672f-b7a2-4cc1-9ade-48baa8276f16

import Mathlib
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (H : ℝ≥0) :
    let S : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    let U : Set ℝ := {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω}
    let μ := (dividendMeasure D ω).restrict S
    NullSingletonClass (μ.restrict U) := by 
  dsimp only
  refine ⟨fun t => ?_⟩
  rw [Measure.restrict_apply (measurableSet_singleton _)]
  by_cases hu : rightLimit D t.toNNReal ω = D t.toNNReal ω
  · rw [Set.singleton_inter_of_mem (show t ∈ {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω} from hu)]
    rw [Measure.restrict_apply (measurableSet_singleton _)]
    by_cases hs : t ∈ paymentTimes (ruinTime X x D ω) ∩ Iic (H : ℝ)
    · rw [Set.singleton_inter_of_mem hs]
      have ht : 0 ≤ t := hs.1.1
      have h := dividendMeasure_singleton_eq_rightLimit_sub D hD ω t.toNNReal
      rw [Real.coe_toNNReal _ ht, hu, sub_self, ENNReal.ofReal_zero] at h
      exact h
    · rw [Set.singleton_inter_of_notMem hs, measure_empty]
  · rw [Set.singleton_inter_of_notMem (show t ∉ {t : ℝ | rightLimit D t.toNNReal ω = D t.toNNReal ω} from hu), measure_empty]
