-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_no_positive_atoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:50:58.051803+00:00
-- url     : https://prove2.me/submissions/fe297e32-e9cf-433e-b70f-88aecbd86964

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_leftLim_eq_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ) (ht : 0 < t) :
    (dividendMeasure (runningSup X) ω) ({t} : Set ℝ) = 0 := by
  obtain ⟨hMono, hMeasure⟩ :=
    runningSup_dividendMeasure_eq_stieltjes X ω
  have hSf :
      hMono.stieltjesFunction =
        (fun r : ℝ => runningSup X r.toNNReal ω) := by
    funext r
    simp only [Monotone.stieltjesFunction_eq]
    exact runningSup_realTime_rightLim_eq X ω r
  rw [hMeasure, StieltjesFunction.measure_singleton, hSf]
  rw [runningSup_realTime_leftLim_eq_pos X ω t ht]
  simp
