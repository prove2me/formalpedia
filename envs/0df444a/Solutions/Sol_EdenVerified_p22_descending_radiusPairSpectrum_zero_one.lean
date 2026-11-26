-- Prove2me | solution 1 for EdenVerified.p22_descending_radiusPairSpectrum_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:33:56.660802+00:00
-- url     : https://prove2.me/submissions/e438cbe1-46a0-44d0-a35f-f47c72bc685b

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_descending_radiusPairSpectrum_zero_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    descending (radiusPairSpectrum c 0 1) = ![2, 0, -2, -2, -c] :=
  @Eden.descending_radiusPairSpectrum_zero_one
end EdenVerified
