-- Prove2me | solution 1 for EdenVerified.p25_stationary_radii_of_evolution_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:17:02.591344+00:00
-- url     : https://prove2.me/submissions/ed07bc98-717c-4941-9e0c-0bb2d975e4eb

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_stationary_radii_of_evolution_return


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (c : ℝ) {t : ℝ} (ht : 0 < t)
    {p : PhaseSpace} (h : evolution c t p = p),
    (radiusSq₁ p = 0 ∨ radiusSq₁ p = 1 ∨ radiusSq₁ p = 2) ∧
    (radiusSq₂ p = 0 ∨ radiusSq₂ p = 1 ∨ radiusSq₂ p = 2) :=
  @Eden.stationary_radii_of_evolution_return
end EdenVerified
