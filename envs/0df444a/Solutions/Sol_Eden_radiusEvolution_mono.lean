-- Prove2me | solution 1 for Eden.radiusEvolution_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:05.206322+00:00
-- url     : https://prove2.me/submissions/90d0258f-21d4-4de7-bc62-fef7093fd38f

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
import Theorems.Thm_Eden_strictMono_squaredRadiusEvolution


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {t r R : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) (hrR : r ≤ R) :
    radiusEvolution t r ≤ radiusEvolution t R := by
  apply Real.sqrt_le_sqrt
  exact (strictMono_squaredRadiusEvolution ht).monotone (by nlinarith)
end Eden
