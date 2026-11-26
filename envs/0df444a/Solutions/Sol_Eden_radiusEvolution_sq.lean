-- Prove2me | solution 1 for Eden.radiusEvolution_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:17.206295+00:00
-- url     : https://prove2.me/submissions/ef750db8-24f6-4bf1-ab82-bb0884fb0a56

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
import Theorems.Thm_Eden_squaredRadiusEvolution_nonneg


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {t : ℝ} (ht : 0 ≤ t) (r : ℝ) :
    radiusEvolution t r ^ 2 = squaredRadiusEvolution t (r ^ 2) :=
  Real.sq_sqrt (squaredRadiusEvolution_nonneg ht (sq_nonneg r))
end Eden
