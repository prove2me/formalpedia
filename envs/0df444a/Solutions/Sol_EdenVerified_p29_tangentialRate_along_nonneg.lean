-- Prove2me | solution 1 for EdenVerified.p29_tangentialRate_along_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:49:13.209606+00:00
-- url     : https://prove2.me/submissions/2642917d-69d3-487a-a832-05ca7fbbbb35

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_tangentialRate_along_nonneg


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {s t : ℝ} (hs₁ : 1 ≤ s) (hs₂ : s ≤ 2)
    (ht : 0 ≤ t),
    0 ≤ tangentialRate (squaredRadiusEvolution t s) :=
  @Eden.tangentialRate_along_nonneg
end EdenVerified
