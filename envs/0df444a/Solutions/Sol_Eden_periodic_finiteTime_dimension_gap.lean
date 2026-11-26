-- Prove2me | solution 1 for Eden.periodic_finiteTime_dimension_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:24.725941+00:00
-- url     : https://prove2.me/submissions/939f21ae-a84c-499f-97ae-f9e9b0310726

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
import Theorems.Thm_Eden_supremum_finiteTimeDimension_periodic
import Theorems.Thm_Eden_globalLyapunovDimension_attractor
import Theorems.Thm_Eden_targetDimension_bounds


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c t : ℝ} (hc : 4 < c) (ht : 0 < t) :
    sSup (finiteTimeDimension c t '' periodicEquilibriumSet c) <
      globalLyapunovDimension c attractor := by
  rw [supremum_finiteTimeDimension_periodic hc ht, globalLyapunovDimension_attractor hc]
  have := (targetDimension_bounds hc).1
  change 4 < 4 + 4 / c at this
  linarith
end Eden
