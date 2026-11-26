-- Prove2me | solution 1 for EdenVerified.p22_descending_radiusPairSpectrum_one_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:34:57.504402+00:00
-- url     : https://prove2.me/submissions/1b4a93f6-1ab9-4814-adf7-f5d3a0b956aa

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_descending_radiusPairSpectrum_one_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 1 1) = ![2, 2, 0, 0, -c] :=
  @Eden.descending_radiusPairSpectrum_one_one
end EdenVerified
