-- Prove2me | solution 1 for Eden.limitingSquaredRadius_of_stationary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:10.807062+00:00
-- url     : https://prove2.me/submissions/5c5d457b-5ae3-46b3-aca6-93d87004b923

import Definitions.Def_Eden_PeriodicSets
import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_FiniteTimeKaplanYorke
import Definitions.Def_Eden_PeriodicDimensions

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {s : ℝ} (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    limitingSquaredRadius s = s := by
  rcases hs with rfl | rfl | rfl <;> norm_num [limitingSquaredRadius]
end Eden
