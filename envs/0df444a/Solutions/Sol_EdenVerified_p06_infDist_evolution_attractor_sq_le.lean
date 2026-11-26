-- Prove2me | solution 1 for EdenVerified.p06_infDist_evolution_attractor_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:12:06.409231+00:00
-- url     : https://prove2.me/submissions/b446ca9b-0d57-4aa5-a318-143ab6c57b3d

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_infDist_evolution_attractor_sq_le


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {M W t : ℝ} (ht : 0 ≤ t)
    (hM : Real.sqrt 2 ≤ M) {p : PhaseSpace}
    (h₁ : Real.sqrt (radiusSq₁ p) ≤ M) (h₂ : Real.sqrt (radiusSq₂ p) ≤ M)
    (hw : |p 4| ≤ W),
    Metric.infDist (evolution c t p) attractor ^ 2 ≤ attractionBound c M W t :=
  @Eden.infDist_evolution_attractor_sq_le
end EdenVerified
