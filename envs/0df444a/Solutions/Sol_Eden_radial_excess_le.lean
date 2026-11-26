-- Prove2me | solution 1 for Eden.radial_excess_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:38:11.220303+00:00
-- url     : https://prove2.me/submissions/d4ea8951-d381-41a3-9816-f90a128d1210

import Definitions.Def_Eden_PhysicalRadius
import Definitions.Def_Eden_AttractorDistance
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_UniformAttraction
import Theorems.Thm_Eden_radiusEvolution_ge_sqrt_two
import Theorems.Thm_Eden_radiusEvolution_mono


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution {t r M : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r)
    (hrM : r ≤ M) (hM : Real.sqrt 2 ≤ M) :
    max (radiusEvolution t r - Real.sqrt 2) 0 ≤ radiusEvolution t M - Real.sqrt 2 := by
  apply max_le
  · linarith [radiusEvolution_mono ht hr hrM]
  · linarith [radiusEvolution_ge_sqrt_two ht hM]
end Eden
