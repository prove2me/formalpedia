-- Prove2me | solution 1 for EdenVerified.p14_rates_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:25:12.355846+00:00
-- url     : https://prove2.me/submissions/c00f6deb-6d44-4be8-a750-6411f6738de8

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_rates_sum


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (s : ℝ),
    radialRate s + tangentialRate s = 2 - 6 * (s - 1) ^ 2 :=
  @Eden.rates_sum
end EdenVerified
