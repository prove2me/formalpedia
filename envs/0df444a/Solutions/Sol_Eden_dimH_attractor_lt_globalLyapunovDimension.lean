-- Prove2me | solution 1 for Eden.dimH_attractor_lt_globalLyapunovDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:16:03.884057+00:00
-- url     : https://prove2.me/submissions/86a37d79-3efe-404e-91b7-b4e3a9fc802e

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_ExponentSums
import Definitions.Def_Eden_HausdorffDimensions
import Definitions.Def_Eden_TorusDirections
import Theorems.Thm_Eden_dimH_attractor
import Theorems.Thm_Eden_globalLyapunovDimension_attractor


set_option autoImplicit true
noncomputable section
open Set Filter Topology MeasureTheory
open Eden
namespace Eden
theorem _root_.solution {c : ℝ} (hc : 4 < c) :
    (dimH attractor).toReal < globalLyapunovDimension c attractor := by
  rw [dimH_attractor, globalLyapunovDimension_attractor hc]
  norm_num
  positivity
end Eden
