-- Prove2me | solution 1 for EdenVerified.p15_tangentialRate_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:25:46.322286+00:00
-- url     : https://prove2.me/submissions/b409e609-c3a5-4bd6-ad37-8efd26fd1867

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tangentialRate_lower_bound


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {s : ℝ} (hs₀ : 0 ≤ s) (hs₂ : s ≤ 2),
    -2 ≤ tangentialRate s :=
  @Eden.tangentialRate_lower_bound
end EdenVerified
