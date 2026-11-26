-- Prove2me | solution 1 for EdenVerified.p23_asymptoticDimension_eq_target_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:37:45.695249+00:00
-- url     : https://prove2.me/submissions/59c16f64-bd42-430b-a0a2-ff0ae57b93d8

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_eq_target_iff


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c) {p : PhaseSpace}
    (hp : p ∈ attractor),
    asymptoticDimension c p = targetDimension c ↔ p ∈ torus :=
  @Eden.asymptoticDimension_eq_target_iff
end EdenVerified
