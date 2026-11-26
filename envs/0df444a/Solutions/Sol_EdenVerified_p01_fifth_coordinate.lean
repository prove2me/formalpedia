-- Prove2me | solution 1 for EdenVerified.p01_fifth_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:22:00.386682+00:00
-- url     : https://prove2.me/submissions/2f761069-fe8b-4e53-80e8-2eafffc73615

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution

set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c t : ℝ) (p : PhaseSpace) :
    evolution c t p 4 = Real.exp (-c*t)*p 4 := rfl
end EdenVerified
