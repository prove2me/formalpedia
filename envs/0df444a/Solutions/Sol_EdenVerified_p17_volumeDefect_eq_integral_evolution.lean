-- Prove2me | solution 1 for EdenVerified.p17_volumeDefect_eq_integral_evolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:27:12.652508+00:00
-- url     : https://prove2.me/submissions/2ff34ef8-67fe-402f-b511-93db1fef0044

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_volumeDefect_eq_integral_evolution


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 ≤ t)
    (p : PhaseSpace),
    volumeDefect t p = ∫ τ in (0 : ℝ)..t,
      ((radiusSq₁ (evolution c τ p) - 1) ^ 2 +
        (radiusSq₂ (evolution c τ p) - 1) ^ 2) :=
  @Eden.volumeDefect_eq_integral_evolution
end EdenVerified
