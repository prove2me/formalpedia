-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_exponential_damping_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:25:53.301421+00:00
-- url     : https://prove2.me/submissions/6226df64-cb1a-44b2-a505-b397c19e7253

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_AvramDividend_Classical_causal_exponential_weighted_kernel_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (K : ℝ → ℝ) (w : ℝ) (hw : 0 < w)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => Real.exp (-w * t) * K t)
      (Ioi (0 : ℝ)) volume := by
  exact causal_exponential_weighted_kernel_integrable K w hw.le hK
