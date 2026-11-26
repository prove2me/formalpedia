-- Prove2me | solution 1 for Eden.radiusEvolution_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:37.855369+00:00
-- url     : https://prove2.me/submissions/b5357b3a-7240-4b13-a241-dd045c7d06f8

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
import Theorems.Thm_Eden_squaredRadiusEvolution_pos_iff


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {t r : ℝ} (ht : 0 ≤ t) (hr : 0 < r) :
    0 < radiusEvolution t r :=
  Real.sqrt_pos.2 ((squaredRadiusEvolution_pos_iff ht).2 (sq_pos_of_pos hr))
end Eden
