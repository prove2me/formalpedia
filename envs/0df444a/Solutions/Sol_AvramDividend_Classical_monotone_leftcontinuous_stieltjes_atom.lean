-- Prove2me | solution 1 for AvramDividend.Classical.monotone_leftcontinuous_stieltjes_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:52:01.976263+00:00
-- url     : https://prove2.me/submissions/5d1362ae-9bfc-48c1-8e87-308101bad3fd

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (f : ℝ → ℝ) (hf : Monotone f)
    (hleft : ∀ t : ℝ, ContinuousWithinAt f (Iic t) t)
    (t : ℝ) :
    hf.stieltjesFunction.measure {t} =
      ENNReal.ofReal (Function.rightLim f t - f t) := by
  have hLim :
      Function.leftLim (Function.rightLim f) t =
        Function.leftLim f t :=
    leftLim_rightLim (hf.tendsto_leftLim t)
  have hVal : Function.leftLim f t = f t :=
    (hleft t).leftLim_eq
  calc
    hf.stieltjesFunction.measure {t} =
        ENNReal.ofReal
          (hf.stieltjesFunction t -
            Function.leftLim (hf.stieltjesFunction : ℝ → ℝ) t) :=
      hf.stieltjesFunction.measure_singleton t
    _ = ENNReal.ofReal (Function.rightLim f t - f t) := by
      change ENNReal.ofReal
        (Function.rightLim f t -
          Function.leftLim (Function.rightLim f) t) =
          ENNReal.ofReal (Function.rightLim f t - f t)
      rw [hLim, hVal]
