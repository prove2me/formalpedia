-- Prove2me | solution 1 for Eden.supremum_finiteTimeDimension_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:06.518242+00:00
-- url     : https://prove2.me/submissions/b1ad4ecc-fbc2-420e-9c69-dcff2d36d892

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
import Theorems.Thm_Eden_finiteTimeDimension_periodic_isGreatest

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    sSup (finiteTimeDimension c t '' periodicEquilibriumSet c) = 3 :=
  (finiteTimeDimension_periodic_isGreatest hc ht).csSup_eq
end Eden
