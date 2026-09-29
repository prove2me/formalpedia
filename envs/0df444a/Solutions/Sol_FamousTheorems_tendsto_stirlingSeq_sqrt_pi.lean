-- Prove2me | solution 1 for FamousTheorems.tendsto_stirlingSeq_sqrt_pi
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:37.09201+00:00
-- url     : https://prove2.me/submissions/0a582df5-0fe8-4d1e-859a-a2915d206d0f

import Mathlib

theorem solution :
    Filter.Tendsto Stirling.stirlingSeq Filter.atTop (nhds (Real.sqrt Real.pi)) :=
  Stirling.tendsto_stirlingSeq_sqrt_pi
