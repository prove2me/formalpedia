-- Prove2me | solution 1 for EdenVerified.p23_asymptoticDimension_eq_target_iff_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:37:17.836801+00:00
-- url     : https://prove2.me/submissions/a6145b61-7bf4-44ce-a97b-a87922bc864f

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_eq_target_iff_radii


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c) (p : PhaseSpace),
    asymptoticDimension c p = targetDimension c ↔ radiusSq₁ p = 1 ∧ radiusSq₂ p = 1 :=
  @Eden.asymptoticDimension_eq_target_iff_radii
end EdenVerified
