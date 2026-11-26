-- Prove2me | solution 1 for EdenVerified.p22_kaplanYorkeDimension_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:35:38.544862+00:00
-- url     : https://prove2.me/submissions/eca08992-9abc-4e7e-8eb2-48c189bd011c

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 0, -2, -2, -c] = 3 :=
  @Eden.kaplanYorkeDimension_zero_one
end EdenVerified
