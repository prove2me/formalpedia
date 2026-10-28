-- Prove2me | solution 1 for AvramDividend.Classical.chat04_continuous_causal_convolution_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:26:45.762242+00:00
-- url     : https://prove2.me/submissions/fe96da92-e6f9-4283-836a-63be9d3cb8ab

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A continuous causal convolution kernel is integrable on the positive axis. -/
theorem solution
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hzero : ∀ y : ℝ, y < 0 → g y = 0) (x : ℝ) :
    IntegrableOn (fun y : ℝ => f y * g (x - y)) (Ioi (0 : ℝ)) := by
  have hcont : Continuous (fun y : ℝ => f y * g (x - y)) :=
    hf.mul (hg.comp (continuous_const.sub continuous_id))
  have hcompact : IntegrableOn (fun y : ℝ => f y * g (x - y))
      (Icc (0 : ℝ) x) := hcont.integrableOn_Icc
  apply hcompact.of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
  filter_upwards [] with y hy
  have hygt : x < y := by
    by_contra hnot
    exact hy.2 ⟨le_of_lt hy.1, le_of_not_gt hnot⟩
  rw [hzero (x - y) (by linarith)]
  ring
