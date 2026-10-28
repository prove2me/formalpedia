-- Prove2me | solution 1 for AvramDividend.Classical.continuous_monotone_real_has_stieltjes_cumulative_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:11:26.42638+00:00
-- url     : https://prove2.me/submissions/715ee6f0-87a2-486d-a14e-bf31e8ef98d4

import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped ENNReal

/-- A continuous monotone real function vanishing at minus infinity is a Stieltjes CDF. -/
theorem solution
    (F : ℝ → ℝ)
    (hMono : Monotone F)
    (hCont : Continuous F)
    (hBot : Tendsto F atBot (nhds 0)) :
    ∃ μ : Measure ℝ, ∀ x : ℝ, μ (Iic x) = ENNReal.ofReal (F x) := by
  let G : StieltjesFunction ℝ := hMono.stieltjesFunction
  have hG : ∀ x : ℝ, G.toFun x = F x := by
    intro x
    change (hMono.stieltjesFunction).toFun x = F x
    rw [Monotone.stieltjesFunction_eq hMono x]
    exact hCont.continuousAt.continuousWithinAt.rightLim_eq
  have hFun : G.toFun = F := funext hG
  have hGbot : Tendsto G.toFun atBot (nhds (0 : ℝ)) := by
    simpa only [hFun] using hBot
  refine ⟨G.measure, ?_⟩
  intro x
  have hm := G.measure_Iic hGbot x
  simpa [hG x] using hm
