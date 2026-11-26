-- Prove2me | solution 1 for EdenVerified.s04_fderiv_evolution_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:37:48.400581+00:00
-- url     : https://prove2.me/submissions/4bc339f3-4a63-494e-a9b2-fc52f9a4dddf

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_fderiv_evolution_add


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (p : PhaseSpace),
    fderiv ℝ (evolution c (s + t)) p =
      (fderiv ℝ (evolution c t) (evolution c s p)).comp (fderiv ℝ (evolution c s) p) :=
  @Eden.fderiv_evolution_add
end EdenVerified
