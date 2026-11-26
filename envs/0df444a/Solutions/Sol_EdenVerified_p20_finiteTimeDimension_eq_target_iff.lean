-- Prove2me | solution 1 for EdenVerified.p20_finiteTimeDimension_eq_target_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:29:57.250435+00:00
-- url     : https://prove2.me/submissions/891d229e-1ec5-4984-ab49-9206e4688768

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_finiteTimeDimension_eq_target_iff


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
    finiteTimeDimension c t p = targetDimension c ↔ p ∈ torus :=
  @Eden.finiteTimeDimension_eq_target_iff
end EdenVerified
