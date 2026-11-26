-- Prove2me | solution 1 for EdenVerified.p02_radialField_neg_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:05:55.730159+00:00
-- url     : https://prove2.me/submissions/d0a4f5aa-619f-440c-b9db-fae3a37c1da0

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radialField_neg_above


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {r : ℝ} (hr : Real.sqrt 2 < r),
    radialField r < 0 :=
  @Eden.radialField_neg_above
end EdenVerified
