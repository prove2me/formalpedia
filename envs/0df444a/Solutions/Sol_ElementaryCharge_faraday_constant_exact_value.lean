-- Prove2me | solution 1 for ElementaryCharge.faraday_constant_exact_value
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T16:36:14.598397+00:00
-- url     : https://prove2.me/submissions/c7b251b6-7f6c-44e9-ac26-8f5216eccd6c

import Mathlib
import Definitions.Def_elementary_charge_si_constants

open ElementaryCharge

theorem solution :
    faradayConstant avogadroSI eSI = 964853321233100184 / 10 ^ 13 := by
  norm_num [faradayConstant, avogadroSI, eSI]
