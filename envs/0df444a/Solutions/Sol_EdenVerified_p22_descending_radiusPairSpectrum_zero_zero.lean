-- Prove2me | solution 1 for EdenVerified.p22_descending_radiusPairSpectrum_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:33:53.1715+00:00
-- url     : https://prove2.me/submissions/d8d44ae3-a9cd-403b-ae7f-b91feb2eff86

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_zero


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 0) = ![-2, -2, -2, -2, -c] :=
  @Eden.descending_radiusPairSpectrum_zero_zero
end EdenVerified
