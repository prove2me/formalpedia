-- Prove2me | solution 1 for EdenVerified.p22_kaplanYorkeDimension_two_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:36:26.139919+00:00
-- url     : https://prove2.me/submissions/da09e05f-4406-4c94-b740-8cee7762490a

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_kaplanYorkeDimension_two_two


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![0, 0, -4, -4, -c] = 2 :=
  @Eden.kaplanYorkeDimension_two_two
end EdenVerified
