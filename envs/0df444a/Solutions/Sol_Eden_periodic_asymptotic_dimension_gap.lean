-- Prove2me | solution 1 for Eden.periodic_asymptotic_dimension_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:19.883672+00:00
-- url     : https://prove2.me/submissions/04cdd0e8-7f24-4652-a4ab-cf9d7dce728a

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
import Theorems.Thm_Eden_supremum_asymptoticDimension_periodic
import Theorems.Thm_Eden_globalLyapunovDimension_attractor
import Theorems.Thm_Eden_targetDimension_bounds


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    sSup (asymptoticDimension c '' periodicEquilibriumSet c) <
      globalLyapunovDimension c attractor := by
  rw [supremum_asymptoticDimension_periodic hc, globalLyapunovDimension_attractor hc]
  have := (targetDimension_bounds hc).1
  change 4 < 4 + 4 / c at this
  linarith
end Eden
