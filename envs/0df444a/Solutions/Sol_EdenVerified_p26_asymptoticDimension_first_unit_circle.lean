-- Prove2me | solution 1 for EdenVerified.p26_asymptoticDimension_first_unit_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:19:48.109065+00:00
-- url     : https://prove2.me/submissions/e954af5a-a290-46b9-aacf-8bef6262dd9f

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_first_unit_circle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 1),
    asymptoticDimension c p = 3 :=
  @Eden.asymptoticDimension_first_unit_circle
end EdenVerified
