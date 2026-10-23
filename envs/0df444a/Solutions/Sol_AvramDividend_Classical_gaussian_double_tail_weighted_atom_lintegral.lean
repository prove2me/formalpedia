-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_weighted_atom_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:01:24.769612+00:00
-- url     : https://prove2.me/submissions/b4a7ced3-f4fb-496a-9ad4-a13375b204f6

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_unweighted_atom_lintegral
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (φ z : ℝ) (hz : 0 ≤ z) :
    (∫⁻ t in Ioc (0 : ℝ) z,
      ENNReal.ofReal (Real.exp (-(φ * z))) *
        ENNReal.ofReal (z - t) ∂volume) =
      ENNReal.ofReal (Real.exp (-(φ * z))) *
        ENNReal.ofReal (z ^ 2 / 2) := by
  have hmeas : Measurable
      (fun t : ℝ => ENNReal.ofReal (z - t)) := by fun_prop
  rw [lintegral_const_mul
    (ENNReal.ofReal (Real.exp (-(φ * z)))) hmeas]
  rw [gaussian_double_tail_unweighted_atom_lintegral z hz]
