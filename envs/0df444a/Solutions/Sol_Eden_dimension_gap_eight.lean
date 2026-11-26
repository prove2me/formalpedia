-- Prove2me | solution 1 for Eden.dimension_gap_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:25.498604+00:00
-- url     : https://prove2.me/submissions/f8f84f97-4deb-45c6-85ee-a5f777542069

import Definitions.Def_Eden_PeriodicDimensions
import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_PeriodicGap
import Theorems.Thm_Eden_asymptoticDimension_periodic_isGreatest
import Theorems.Thm_Eden_finiteTimeDimension_periodic_isGreatest
import Theorems.Thm_Eden_globalLyapunovDimension_attractor_eight


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    globalLyapunovDimension 8 attractor = 9 / 2 ∧
      IsGreatest (asymptoticDimension 8 '' periodicEquilibriumSet 8) 3 ∧
      IsGreatest (finiteTimeDimension 8 t '' periodicEquilibriumSet 8) 3 :=
  ⟨globalLyapunovDimension_attractor_eight,
    asymptoticDimension_periodic_isGreatest (by norm_num),
    finiteTimeDimension_periodic_isGreatest (by norm_num) ht⟩
end Eden
