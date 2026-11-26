-- Prove2me | solution 1 for EdenVerified.p22_kaplanYorkeDimension_one_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:36:17.079813+00:00
-- url     : https://prove2.me/submissions/02b4f313-443e-4122-b725-80c414967fb7

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_kaplanYorkeDimension_one_two


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 0, 0, -4, -c] = 7 / 2 :=
  @Eden.kaplanYorkeDimension_one_two
end EdenVerified
