-- Prove2me | solution 1 for EdenVerified.p22_kaplanYorkeDimension_zero_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:35:53.66878+00:00
-- url     : https://prove2.me/submissions/ee3b57de-aac2-4c0a-a36e-6ac7da8dfa75

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_kaplanYorkeDimension_zero_two


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![0, -2, -2, -4, -c] = 1 :=
  @Eden.kaplanYorkeDimension_zero_two
end EdenVerified
