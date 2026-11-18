-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_mark_intensity_normalisation_rate_bridge_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:12:44.4938+00:00
-- url     : https://prove2.me/submissions/d43aa04b-68ec-4628-bd3d-1dafaff2a2b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- The intensity and one-mark transform determine the compound-Poisson exponent. -/
theorem solution (t lambda r markMoment markIntegral exponent : ℝ)
    (hr : r = t * lambda)
    (hMoment : markMoment * lambda = markIntegral)
    (hExponent : exponent = markIntegral - lambda) :
    r * (markMoment - 1) = t * exponent := by
  rw [hr, hExponent, ← hMoment]
  ring
