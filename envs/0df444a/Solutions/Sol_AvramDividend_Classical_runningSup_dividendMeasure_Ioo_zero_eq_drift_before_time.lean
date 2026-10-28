-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_Ioo_zero_eq_drift_before_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:28:25.417823+00:00
-- url     : https://prove2.me/submissions/9bd42f95-c191-493c-ad6e-dd5405f5bfe4

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_before_time
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_positive_atoms
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ)
    (hT : 0 < T)
    (hPath : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      runningSup X u.toNNReal ω = X.drift * u) :
    (dividendMeasure (runningSup X) ω) (Ioo 0 T) =
      ENNReal.ofReal (X.drift * T) := by
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  have hAtom : μ ({T} : Set ℝ) = 0 :=
    runningSup_dividendMeasure_no_positive_atoms X ω T hT
  have hset : (Ioc (0 : ℝ) T) \ {T} = Ioo 0 T := by
    ext x
    simp only [Set.mem_diff, Set.mem_Ioc, Set.mem_singleton_iff, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨hx0, hxT⟩, hxne⟩
      exact ⟨hx0, lt_of_le_of_ne hxT hxne⟩
    · rintro ⟨hx0, hxT⟩
      exact ⟨⟨hx0, le_of_lt hxT⟩, ne_of_lt hxT⟩
  have hdiff : μ (Ioo (0 : ℝ) T) = μ (Ioc 0 T) := by
    rw [← hset]
    exact measure_sdiff_null (μ := μ) (s := Ioc (0 : ℝ) T)
      (t := ({T} : Set ℝ)) hAtom
  have hIoc := runningSup_dividendMeasure_Ioc_eq_drift_before_time
    X ω T 0 T hPath (le_refl 0) (le_of_lt hT) (le_refl T)
  change μ (Ioo 0 T) = ENNReal.ofReal (X.drift * T)
  calc
    μ (Ioo 0 T) = μ (Ioc 0 T) := hdiff
    _ = ENNReal.ofReal (X.drift * T) := by simpa using hIoc
