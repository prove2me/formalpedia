-- Prove2me | solution 1 for EdenVerified.p26_asymptoticDimension_first_outer_circle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:20:08.127314+00:00
-- url     : https://prove2.me/submissions/e19a5d9a-8f40-4856-a0e4-9413c2c73f1c

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_asymptoticDimension_first_outer_circle


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ {c : ℝ} (hc : 4 < c)
    {p : PhaseSpace} (hp : p ∈ firstCircle 2),
    asymptoticDimension c p = 1 :=
  @Eden.asymptoticDimension_first_outer_circle
end EdenVerified
