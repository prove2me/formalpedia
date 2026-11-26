-- Prove2me | solution 1 for Eden.supremum_asymptoticDimension_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:13.253488+00:00
-- url     : https://prove2.me/submissions/e724a841-2ef7-496b-bda1-d42e609deeb8

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
import Theorems.Thm_Eden_asymptoticDimension_periodic_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) = 3 :=
  (asymptoticDimension_periodic_isGreatest hc).csSup_eq
end Eden
