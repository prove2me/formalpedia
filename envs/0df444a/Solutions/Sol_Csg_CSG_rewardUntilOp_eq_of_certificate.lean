-- Prove2me | solution 1 for Csg.CSG.rewardUntilOp_eq_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:48:24.324204+00:00
-- url     : https://prove2.me/submissions/6fecf43d-298f-411c-86ed-ed21b623ffcf

import Definitions.Def_Csg_Basic
import Definitions.Def_Csg_RewardUntilCertificate

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal] (v : S → ℝ)
    (hfixed : C.rewardUntilStep goal v = v)
    (huniq : ∀ w : S → ℝ, C.rewardUntilStep goal w = w → w = v) :
    ∃! w : S → ℝ, C.rewardUntilStep goal w = w :=
  ⟨v, hfixed, huniq⟩
end Csg.CSG
