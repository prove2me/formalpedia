-- Prove2me | solution 1 for ComparativeAdvantage.ricardo_advantages
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:42:26.944896+00:00
-- url     : https://prove2.me/submissions/4db94bd6-6f37-4fc5-b422-54afb02a9a64

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ComparativeAdvantage

theorem solution :
    portugal.aLC < england.aLC ∧ portugal.aLW < england.aLW ∧
    HasComparativeAdvantageInCloth england portugal ∧
    ¬ HasComparativeAdvantageInCloth portugal england := by
  unfold HasComparativeAdvantageInCloth portugal england
  norm_num
