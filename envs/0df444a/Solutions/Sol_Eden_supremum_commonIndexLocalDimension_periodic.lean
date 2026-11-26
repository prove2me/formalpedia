-- Prove2me | solution 1 for Eden.supremum_commonIndexLocalDimension_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:39.302895+00:00
-- url     : https://prove2.me/submissions/43d0bed9-1d4a-4cb1-b764-271ef02ba390

import Definitions.Def_Eden_CommonIndex
import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_CommonIndexPeriodic
import Theorems.Thm_Eden_commonIndexLocalDimension_periodic_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    sSup (commonIndexLocalDimension c '' periodicEquilibriumSet c) = 4 - 2 / c :=
  (commonIndexLocalDimension_periodic_isGreatest hc).csSup_eq
end Eden
