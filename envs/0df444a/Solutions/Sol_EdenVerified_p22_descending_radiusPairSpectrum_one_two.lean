-- Prove2me | solution 1 for EdenVerified.p22_descending_radiusPairSpectrum_one_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:35:02.007432+00:00
-- url     : https://prove2.me/submissions/1029f622-6950-4507-b563-7f8ab28dbc2e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_descending_radiusPairSpectrum_one_two


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 1 2) = ![2, 0, 0, -4, -c] :=
  @Eden.descending_radiusPairSpectrum_one_two
end EdenVerified
