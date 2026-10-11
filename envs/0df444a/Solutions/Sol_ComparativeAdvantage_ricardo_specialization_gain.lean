-- Prove2me | solution 1 for ComparativeAdvantage.ricardo_specialization_gain
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:44:27.745584+00:00
-- url     : https://prove2.me/submissions/f144867b-f541-485b-a828-b1076387d1d1

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ComparativeAdvantage

theorem solution :
    england.aLC * 1 + england.aLW * 1 = england.L ∧
    portugal.aLC * 1 + portugal.aLW * 1 = portugal.L ∧
    england.L / england.aLC = 2.2 ∧ portugal.L / portugal.aLW = 2.125 ∧
    1 + 1 < england.L / england.aLC ∧
    1 + 1 < portugal.L / portugal.aLW := by
  norm_num [england, portugal]
