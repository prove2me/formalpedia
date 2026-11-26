-- Prove2me | solution 1 for EdenVerified.p02_radialField_neg_below_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:42.394386+00:00
-- url     : https://prove2.me/submissions/7cd6f378-c1f3-4938-8852-9920dce22e75

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_radialField_neg_below_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {r : ℝ} (hr : 0 < r) (hr₁ : r < 1),
    radialField r < 0 :=
  @Eden.radialField_neg_below_one
end EdenVerified
