-- Prove2me | solution 1 for EdenVerified.D01_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:02.379029+00:00
-- url     : https://prove2.me/submissions/636ed5c1-1c5c-4c41-8fd8-e530f2af2e67

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_targetDimension_bounds


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    0 < c ∧ 4 < 4 + 4 / c ∧ 4 + 4 / c < 5 :=
  ⟨by linarith, targetDimension_bounds hc⟩
end EdenVerified
