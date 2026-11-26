-- Prove2me | solution 1 for EdenVerified.p20_singularValues_on_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:29:50.842057+00:00
-- url     : https://prove2.me/submissions/502bd008-33d8-42a7-9347-85419327bdb2

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValues_on_torus


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus),
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      ![Real.exp (2 * t), Real.exp (2 * t), 1, 1, Real.exp (-c * t)] :=
  @Eden.singularValues_on_torus
end EdenVerified
