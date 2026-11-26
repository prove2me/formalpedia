-- Prove2me | solution 1 for EdenVerified.p22_kaplanYorkeDimension_one_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:35:56.540807+00:00
-- url     : https://prove2.me/submissions/12ff8f9e-066d-46c8-a4b5-806ac7d1c822

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_kaplanYorkeDimension_one_one


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c),
    kaplanYorkeDimension ![2, 2, 0, 0, -c] = targetDimension c :=
  @Eden.kaplanYorkeDimension_one_one
end EdenVerified
