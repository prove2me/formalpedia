-- Prove2me | solution 1 for EdenVerified.p26_normalizedLogSingularValues_outer_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:19:20.9898+00:00
-- url     : https://prove2.me/submissions/7784ccab-24ca-469f-9856-a4842e2e559e

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_normalizedLogSingularValues_outer_circle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 2 ∨ p ∈ secondCircle 2),
    normalizedLogSingularValues c t p = ![0, -2, -2, -4, -c] :=
  @Eden.normalizedLogSingularValues_outer_circle
end EdenVerified
