-- Prove2me | solution 1 for EdenVerified.p26_normalizedLogSingularValues_unit_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:19:17.168796+00:00
-- url     : https://prove2.me/submissions/ae1f60e5-6025-4b36-82c2-59b1fcef7da0

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_normalizedLogSingularValues_unit_circle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c t : ℝ} (hc : 4 < c)
    (ht : 0 < t) {p : PhaseSpace} (hp : p ∈ firstCircle 1 ∨ p ∈ secondCircle 1),
    normalizedLogSingularValues c t p = ![2, 0, -2, -2, -c] :=
  @Eden.normalizedLogSingularValues_unit_circle
end EdenVerified
