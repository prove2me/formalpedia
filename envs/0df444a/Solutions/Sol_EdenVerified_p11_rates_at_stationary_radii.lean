-- Prove2me | solution 1 for EdenVerified.p11_rates_at_stationary_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:15:21.435158+00:00
-- url     : https://prove2.me/submissions/9d836c5e-e9e9-4d35-94b3-049e9b6ba1d3

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_rates_at_stationary_radii


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    radialRate 0 = -2 ∧ tangentialRate 0 = -2 ∧
    radialRate 1 = 2 ∧ tangentialRate 1 = 0 ∧
    radialRate 2 = -4 ∧ tangentialRate 2 = 0 :=
  @Eden.rates_at_stationary_radii
end EdenVerified
