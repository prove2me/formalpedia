-- Prove2me | solution 1 for FamousTheorems.liouville_numbers_measure_zero
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:20:21.727744+00:00
-- url     : https://prove2.me/submissions/1ef9987e-4e1e-4250-90ba-058b9cb4ecd8

import Mathlib

theorem solution : MeasureTheory.volume {x : ℝ | Liouville x} = 0 :=
  volume_setOfPred_liouville
