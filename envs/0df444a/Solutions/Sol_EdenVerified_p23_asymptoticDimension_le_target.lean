-- Prove2me | solution 1 for EdenVerified.p23_asymptoticDimension_le_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:36:58.49593+00:00
-- url     : https://prove2.me/submissions/4302dc33-1195-4294-b4c7-3abbc5c27d07

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_le_target


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c) (p : PhaseSpace),
    asymptoticDimension c p ≤ targetDimension c :=
  @Eden.asymptoticDimension_le_target
end EdenVerified
