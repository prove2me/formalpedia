-- Prove2me | solution 1 for EdenVerified.p25_one_radius_zero_of_evolution_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:17:24.043241+00:00
-- url     : https://prove2.me/submissions/d5b3c80f-2e1c-4fcd-b05f-6350fc958940

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_one_radius_zero_of_evolution_return


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
    radiusSq₁ p = 0 ∨ radiusSq₂ p = 0 :=
  @Eden.one_radius_zero_of_evolution_return
end EdenVerified
