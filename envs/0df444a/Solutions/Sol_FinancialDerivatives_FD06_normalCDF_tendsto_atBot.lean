-- Prove2me | solution 1 for FinancialDerivatives.FD06.normalCDF_tendsto_atBot
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:04:16.395349+00:00
-- url     : https://prove2.me/submissions/381d1def-64ba-4a5d-b0d3-d09f480a6d41

import Mathlib
import Definitions.Def_fd06_standardNormalCDF

open FinancialDerivatives.FD06

theorem solution : Filter.Tendsto standardNormalCDF Filter.atBot (nhds 0) := by
  exact ProbabilityTheory.tendsto_cdf_atBot _
