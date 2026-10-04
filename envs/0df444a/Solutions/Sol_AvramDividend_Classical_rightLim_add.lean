-- Prove2me | solution 1 for AvramDividend.Classical.rightLim_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T17:31:09.367531+00:00
-- url     : https://prove2.me/submissions/adb15af1-65de-4be2-b93c-9cf18a43673a

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem solution {f g : ℝ → ℝ} (hf : Monotone f) (hg : Monotone g) (t : ℝ) :
    Function.rightLim f t + Function.rightLim g t = Function.rightLim (f + g) t := by
  have hsum : Tendsto (fun s : ℝ => f s + g s) (𝓝[>] t)
      (𝓝 (Function.rightLim f t + Function.rightLim g t)) := by
    simpa only [Pi.add_apply] using (hf.tendsto_rightLim t).add (hg.tendsto_rightLim t)
  have hlim : Function.rightLim (f + g) t
      = Function.rightLim f t + Function.rightLim g t :=
    rightLim_eq_of_tendsto hsum
  exact hlim.symm
