-- Prove2me | solution 1 for FinancialDerivatives.FD06.normalCDF_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:07:57.964995+00:00
-- url     : https://prove2.me/submissions/3b758297-06de-4703-99ae-65d4500a84dc

import Mathlib
import Definitions.Def_fd06_standardNormalCDF

open FinancialDerivatives.FD06

theorem solution : Monotone standardNormalCDF := by
  exact ProbabilityTheory.monotone_cdf _
