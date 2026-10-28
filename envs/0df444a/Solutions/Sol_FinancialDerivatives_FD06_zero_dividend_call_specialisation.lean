-- Prove2me | solution 1 for FinancialDerivatives.FD06.zero_dividend_call_specialisation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T13:10:40.896223+00:00
-- url     : https://prove2.me/submissions/fe1b03f1-92e3-4d2c-83b0-55f4c337d3ec

import Mathlib
import Definitions.Def_fd06_generalisedCall
import Definitions.Def_fd06_generalisedD1
import Definitions.Def_fd06_generalisedD2
import Definitions.Def_fd06_standardNormalCDF

open FinancialDerivatives.FD06

theorem solution (S K R V : ℝ) : generalisedCall S K R 0 V = S * standardNormalCDF (generalisedD1 S K R 0 V) - K * Real.exp (-R) * standardNormalCDF (generalisedD2 S K R 0 V) := by
  unfold generalisedCall; simp
