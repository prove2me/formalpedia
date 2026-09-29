-- Prove2me | solution 1 for CerednikDrinfeld.Omega.crossRatio_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/f8736cff-1283-56c1-b8bd-96db03dccd41

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_crossRatio_self

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K : Type*} [Field K] (z x y : K) (hzx : z ≠ x) (hzy : z ≠ y) :
    crossRatio z z x y = 1 := by
  have h : (z - y) * (z - x) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hzy) (sub_ne_zero.mpr hzx)
  rw [crossRatio, show (z - x) * (z - y) = (z - y) * (z - x) by ring, div_self h]

end S_CerednikDrinfeld_Omega_crossRatio_self
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_crossRatio_self (solution)
