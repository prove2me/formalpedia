-- Prove2me | solution 1 for EdenVerified.p13_derivativeFactors_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:23:47.251654+00:00
-- url     : https://prove2.me/submissions/4a15cfaa-070e-47df-99da-32e101c984cd

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_derivativeFactors_pos


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) (i : Fin 5),
    0 < derivativeFactors c t p i :=
  @Eden.derivativeFactors_pos
end EdenVerified
