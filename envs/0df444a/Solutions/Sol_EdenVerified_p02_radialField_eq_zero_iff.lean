-- Prove2me | solution 1 for EdenVerified.p02_radialField_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:13.682659+00:00
-- url     : https://prove2.me/submissions/a92ca956-4113-44e8-809a-ac54ff5cfc6e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radialField_eq_zero_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {r : ℝ} (hr : 0 ≤ r),
    radialField r = 0 ↔ r = 0 ∨ r = 1 ∨ r = Real.sqrt 2 :=
  @Eden.radialField_eq_zero_iff
end EdenVerified
