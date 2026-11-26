-- Prove2me | solution 1 for Eden.tendsto_radiusEvolution_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:23:12.442161+00:00
-- url     : https://prove2.me/submissions/d6fe5570-d137-462b-b185-d6f22218db35

import Definitions.Def_Eden_InvariantSets
import Definitions.Def_Eden_GrowthRates
import Definitions.Def_Eden_PhysicalRadius
import Theorems.Thm_Eden_tendsto_squaredRadiusEvolution_of_one_lt


set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {r : ℝ} (hr : 1 < r) :
    Tendsto (fun t => radiusEvolution t r) atTop (𝓝 (Real.sqrt 2)) :=
  (tendsto_squaredRadiusEvolution_of_one_lt (s := r ^ 2) (by nlinarith)).sqrt
end Eden
