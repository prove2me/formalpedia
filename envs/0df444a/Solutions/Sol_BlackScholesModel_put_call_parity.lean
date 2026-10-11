-- Prove2me | solution 1 for BlackScholesModel.put_call_parity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T12:07:50.282133+00:00
-- url     : https://prove2.me/submissions/9d29aac1-4a8a-4bed-8623-a2ac4850d1d5

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_stdNormalCDF_neg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

theorem solution (K r σ T S t : ℝ) :
    putPrice K r σ T S t = K * Real.exp (-r * (T - t)) - S + callPrice K r σ T S t := by
  simp only [putPrice, callPrice, stdNormalCDF_neg]
  ring
