-- Prove2me | solution 1 for Csg.CSG.safetyOp_gfp_eq_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:49:03.670719+00:00
-- url     : https://prove2.me/submissions/63ee7289-3de2-45ae-8816-5d45965ac579

import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_SafetyCertificate
import Theorems.Thm_OrderHom_gfp_eq_of_certificate

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1)
    (hfixed : C.safetyOp safe hr v = v)
    (hub : ∀ b, b ≤ C.safetyOp safe hr b → b ≤ v) :
    (C.safetyOp safe hr).gfp = v :=
  OrderHom.gfp_eq_of_certificate (C.safetyOp safe hr) v hfixed hub
end Csg.CSG
