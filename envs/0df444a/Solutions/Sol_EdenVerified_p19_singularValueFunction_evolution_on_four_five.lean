-- Prove2me | solution 1 for EdenVerified.p19_singularValueFunction_evolution_on_four_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:29:45.854821+00:00
-- url     : https://prove2.me/submissions/93b9b581-0d0f-404c-a2ad-0670ad079204

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_singularValueFunction_evolution_on_four_five


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t d : ℝ}
    (hc : 4 ≤ c) (ht : 0 ≤ t) {p : PhaseSpace} (hp : p ∈ attractor)
    (hd₄ : 4 ≤ d) (hd₅ : d ≤ 5),
    singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d =
      Real.exp (4 * t - 6 * volumeDefect t p - c * t * (d - 4)) :=
  @Eden.singularValueFunction_evolution_on_four_five
end EdenVerified
