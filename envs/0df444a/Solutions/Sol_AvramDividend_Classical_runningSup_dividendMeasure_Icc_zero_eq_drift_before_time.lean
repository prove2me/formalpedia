-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_Icc_zero_eq_drift_before_time
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:27:38.15734+00:00
-- url     : https://prove2.me/submissions/1da83749-203e-4cb5-aa1a-b428ee88a56f

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_before_time
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_initial_atom
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
    (hT : 0 ≤ T)
    (hPath : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      runningSup X u.toNNReal ω = X.drift * u) :
    (dividendMeasure (runningSup X) ω) (Icc 0 T) =
      ENNReal.ofReal (X.drift * T) := by
  let μ : Measure ℝ := dividendMeasure (runningSup X) ω
  have hzero : μ ({0} : Set ℝ) = 0 :=
    runningSup_dividendMeasure_zero_initial_atom X 0 (le_refl 0) ω
  have hset : (Icc (0 : ℝ) T) \ {0} = Ioc 0 T := by
    ext x
    simp only [Set.mem_diff, Set.mem_Icc, Set.mem_singleton_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hx0, hxT⟩, hxne⟩
      exact ⟨lt_of_le_of_ne hx0 (Ne.symm hxne), hxT⟩
    · rintro ⟨hx0, hxT⟩
      exact ⟨⟨le_of_lt hx0, hxT⟩, ne_of_gt hx0⟩
  have hdiff : μ (Ioc (0 : ℝ) T) = μ (Icc 0 T) := by
    rw [← hset]
    exact measure_sdiff_null (μ := μ) (s := Icc (0 : ℝ) T)
      (t := ({0} : Set ℝ)) hzero
  have hIoc := runningSup_dividendMeasure_Ioc_eq_drift_before_time
    X ω T 0 T hPath (le_refl 0) hT (le_refl T)
  change μ (Icc 0 T) = ENNReal.ofReal (X.drift * T)
  calc
    μ (Icc 0 T) = μ (Ioc 0 T) := hdiff.symm
    _ = ENNReal.ofReal (X.drift * T) := by simpa using hIoc
