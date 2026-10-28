-- Prove2me | solution 1 for FinancialDerivatives.FD06.normalCDF_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:09:02.050964+00:00
-- url     : https://prove2.me/submissions/629e3c21-20d6-42f4-84b7-eb49c8beb82a

import Mathlib
import Definitions.Def_fd06_standardNormalCDF

open FinancialDerivatives.FD06

theorem solution : Filter.Tendsto standardNormalCDF Filter.atTop (nhds 1) := by
  exact ProbabilityTheory.tendsto_cdf_atTop _
