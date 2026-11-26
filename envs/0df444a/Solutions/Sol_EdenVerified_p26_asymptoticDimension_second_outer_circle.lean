-- Prove2me | solution 1 for EdenVerified.p26_asymptoticDimension_second_outer_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:27.929369+00:00
-- url     : https://prove2.me/submissions/bf394136-74d5-4864-a9b4-8d5062a06585

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_second_outer_circle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 2),
    asymptoticDimension c p = 1 :=
  @Eden.asymptoticDimension_second_outer_circle
end EdenVerified
