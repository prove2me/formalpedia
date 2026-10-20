-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_zero_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:02:40.472971+00:00
-- url     : https://prove2.me/submissions/a2968cef-b998-42fe-a250-5c7955396bc2

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    (dividendMeasure (runningSup X) ω) ({0} : Set ℝ) = 0 := by
  obtain ⟨hMono, hMeasure⟩ :=
    runningSup_dividendMeasure_eq_stieltjes X ω
  have hSf :
      hMono.stieltjesFunction =
        (fun r : ℝ => runningSup X r.toNNReal ω) := by
    funext r
    simp only [Monotone.stieltjesFunction_eq]
    exact runningSup_realTime_rightLim_eq X ω r
  have hLeft :
      Function.leftLim
        (fun r : ℝ => runningSup X r.toNNReal ω) 0 =
          runningSup X 0 ω := by
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hz : r.toNNReal = 0 :=
      Real.toNNReal_of_nonpos (le_of_lt hr)
    simp only [hz]
  rw [hMeasure, StieltjesFunction.measure_singleton, hSf, hLeft]
  simp
