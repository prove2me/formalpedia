-- Prove2me | solution 1 for EdenVerified.p01_planarX_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:04:04.686375+00:00
-- url     : https://prove2.me/submissions/89ceb981-a1df-4de7-88b5-e9b53b58bc50

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_planarX_origin
attribute [local simp] Eden.planarX_origin



set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution :
    ∀ (Ω t : ℝ),
    planarX Ω t 0 0 = 0 :=
  @Eden.planarX_origin
end EdenVerified
