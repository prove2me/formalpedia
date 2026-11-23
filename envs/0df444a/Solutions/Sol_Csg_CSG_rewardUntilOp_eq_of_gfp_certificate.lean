-- Prove2me | solution 1 for Csg.CSG.rewardUntilOp_eq_of_gfp_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:41:43.381246+00:00
-- url     : https://prove2.me/submissions/c7d8c00d-cf02-4de5-87bf-2d7c86c44224

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
    (hub : ∀ w : S → ℝ, C.rewardUntilStep goal w = w → w ≤ v) :
    ∃! w : S → ℝ, C.rewardUntilStep goal w = w ∧
      ∀ u : S → ℝ, C.rewardUntilStep goal u = u → u ≤ w :=
  ⟨v, ⟨hfixed, hub⟩, fun w ⟨hwfixed, hwub⟩ => le_antisymm (hub w hwfixed) (hwub v hfixed)⟩
end Csg.CSG
