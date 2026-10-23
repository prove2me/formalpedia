-- Prove2me | solution 1 for AvramDividend.Classical.causal_constant_kernel_primitive_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T19:11:13.821616+00:00
-- url     : https://prove2.me/submissions/95fc2291-8b42-4bc5-90c1-9188c9c1e955

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (g : ℝ → ℝ) (β x : ℝ) :
    (∫ t in Ioc (0 : ℝ) x,
      (∫ s in Ioc (0 : ℝ) t, β * g s ∂volume) ∂volume) =
    (∫ s in Ioc (0 : ℝ) x,
      β * (∫ t in Ioc (0 : ℝ) s, g t ∂volume) ∂volume) := by
  simp only [integral_const_mul]
