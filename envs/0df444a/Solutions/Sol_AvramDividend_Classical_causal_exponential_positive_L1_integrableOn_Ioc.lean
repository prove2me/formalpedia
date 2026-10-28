-- Prove2me | solution 1 for AvramDividend.Classical.causal_exponential_positive_L1_integrableOn_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T20:33:33.86701+00:00
-- url     : https://prove2.me/submissions/e41d3d9b-6268-4686-a6a8-233f8cecdd63

import Mathlib

open MeasureTheory Set

theorem solution
    (P : ℝ → ℝ) (w x : ℝ)
    (hP : IntegrableOn P (Ioi (0 : ℝ)) volume)
    (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => Real.exp (w * s) * P s)
      (Ioc (0 : ℝ) x) volume := by
  have hP' : IntegrableOn P (Ioc (0 : ℝ) x) volume := hP.mono_set Ioc_subset_Ioi_self
  have hc : ContinuousOn (fun s : ℝ => Real.exp (w * s)) (Icc 0 x) := by fun_prop
  have hI : IntegrableOn P (Icc (0 : ℝ) x) volume := (integrableOn_Icc_iff_integrableOn_Ioc (μ := volume)).mpr hP'
  exact (hI.continuousOn_mul hc isCompact_Icc).mono_set Ioc_subset_Icc_self
