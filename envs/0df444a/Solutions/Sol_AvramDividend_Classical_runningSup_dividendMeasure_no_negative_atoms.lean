-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_dividendMeasure_no_negative_atoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:29:39.734802+00:00
-- url     : https://prove2.me/submissions/1547f370-b316-46c9-928b-44c73852e831

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

/- The real-time extension of the regulator is constant at negative times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ) (ht : t < 0) :
    (dividendMeasure (runningSup X) ω) ({t} : Set ℝ) = 0 := by
  obtain ⟨hMono, hMeasure⟩ :=
    runningSup_dividendMeasure_eq_stieltjes X ω
  have hSf :
      hMono.stieltjesFunction =
        (fun r : ℝ => runningSup X r.toNNReal ω) := by
    funext r
    simp only [Monotone.stieltjesFunction_eq]
    exact runningSup_realTime_rightLim_eq X ω r
  have hAt : t.toNNReal = 0 :=
    Real.toNNReal_of_nonpos (le_of_lt ht)
  have hLeft :
      Function.leftLim
        (fun r : ℝ => runningSup X r.toNNReal ω) t =
          runningSup X 0 ω := by
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≤ 0 :=
      le_trans (le_of_lt hr) (le_of_lt ht)
    have hz : r.toNNReal = 0 := Real.toNNReal_of_nonpos hr0
    simp only [hz]
  rw [hMeasure, StieltjesFunction.measure_singleton, hSf, hLeft]
  simp [hAt]
