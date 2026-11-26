-- Prove2me | solution 1 for EdenVerified.p26_asymptoticDimension_second_unit_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:06.85358+00:00
-- url     : https://prove2.me/submissions/ac4269e0-bc36-474f-abc9-499caee990c9

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_second_unit_circle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ secondCircle 1),
    asymptoticDimension c p = 3 :=
  @Eden.asymptoticDimension_second_unit_circle
end EdenVerified
