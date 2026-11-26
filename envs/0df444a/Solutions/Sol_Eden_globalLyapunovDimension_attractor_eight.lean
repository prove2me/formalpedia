-- Prove2me | solution 1 for Eden.globalLyapunovDimension_attractor_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:12:25.369751+00:00
-- url     : https://prove2.me/submissions/a23d4bf6-7880-481e-9f90-ee5c6d623b41

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
import Theorems.Thm_Eden_globalLyapunovDimension_attractor

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution :
    globalLyapunovDimension 8 attractor = 9 / 2 := by
  rw [globalLyapunovDimension_attractor (by norm_num)]
  norm_num
end Eden
