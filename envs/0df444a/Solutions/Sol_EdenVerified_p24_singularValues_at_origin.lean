-- Prove2me | solution 1 for EdenVerified.p24_singularValues_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:15:47.895154+00:00
-- url     : https://prove2.me/submissions/585112c1-574d-460c-ab92-1b6faa22c885

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValues_at_origin


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 2 ≤ c) (ht : 0 ≤ t),
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) 0).toLinearMap.singularValues i) =
      ![Real.exp (-2 * t), Real.exp (-2 * t), Real.exp (-2 * t),
        Real.exp (-2 * t), Real.exp (-c * t)] :=
  @Eden.singularValues_at_origin
end EdenVerified
