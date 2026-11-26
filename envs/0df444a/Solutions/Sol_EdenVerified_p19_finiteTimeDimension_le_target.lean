-- Prove2me | solution 1 for EdenVerified.p19_finiteTimeDimension_le_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:29:50.181595+00:00
-- url     : https://prove2.me/submissions/cc8659a4-a4a5-4b31-b74e-7f5bdc8dfb87

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_finiteTimeDimension_le_target


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 4 < c) (ht : 0 < t)
    {p : PhaseSpace} (hp : p ∈ attractor),
    finiteTimeDimension c t p ≤ targetDimension c :=
  @Eden.finiteTimeDimension_le_target
end EdenVerified
