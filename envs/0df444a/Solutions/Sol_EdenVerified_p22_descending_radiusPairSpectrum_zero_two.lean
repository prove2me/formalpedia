-- Prove2me | solution 1 for EdenVerified.p22_descending_radiusPairSpectrum_zero_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:34:07.322164+00:00
-- url     : https://prove2.me/submissions/cecd6e28-7819-4a07-bad2-e6b3554af06d

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_two


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 2) = ![0, -2, -2, -4, -c] :=
  @Eden.descending_radiusPairSpectrum_zero_two
end EdenVerified
