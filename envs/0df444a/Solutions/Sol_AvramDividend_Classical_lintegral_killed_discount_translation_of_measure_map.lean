-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_killed_discount_translation_of_measure_map
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:49:01.872309+00:00
-- url     : https://prove2.me/submissions/7a4e588e-80d8-46d4-a07d-9f20ad510cf5

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_lintegral_killed_window_translation_of_measure_map

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical
theorem solution
    (μ ν : Measure ℝ) (u q : ℝ) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμ : μ = Measure.map (fun t : ℝ => u + t) ν)
    (hwindow : ∀ t : ℝ, u + t ∈ A ↔ t ∈ B) :
    (∫⁻ t in A,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
      ENNReal.ofReal (Real.exp (-(q * u))) *
        (∫⁻ t in B,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂ν) := by
  have hm : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-(q * t)))) := by fun_prop
  rw [AvramDividend.Classical.lintegral_killed_window_translation_of_measure_map μ ν u A B hA hB hμ hwindow _ hm,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun t => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring
