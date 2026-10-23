-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_full_kernel_local_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T20:18:57.308805+00:00
-- url     : https://prove2.me/submissions/411c8125-b9cd-4e88-94f7-21784a2ce30f

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A constant plus a positive-halfline integrable function is integrable
on every bounded interval starting at zero. -/
theorem solution (K : ℝ → ℝ) (β R : ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun t : ℝ => β + K t) (Ioc (0 : ℝ) R) volume := by
  have hc : IntegrableOn (fun _ : ℝ => β) (Ioc (0 : ℝ) R) volume := by
    exact integrableOn_const
      (hs := (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) R) < ⊤).ne)
  have hKl : IntegrableOn K (Ioc (0 : ℝ) R) volume :=
    hK.mono_set (by intro t ht; exact ht.1)
  exact hc.add hKl
