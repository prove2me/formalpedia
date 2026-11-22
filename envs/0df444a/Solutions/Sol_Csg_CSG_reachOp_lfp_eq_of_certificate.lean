-- Prove2me | solution 1 for Csg.CSG.reachOp_lfp_eq_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:07:50.017144+00:00
-- url     : https://prove2.me/submissions/8ebbb707-7e45-4056-a19d-261b8502b35e

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_ReachCertificate
import Theorems.Thm_OrderHom_lfp_eq_of_certificate

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (v : S → Set.Icc (0 : ℝ) 1)
    (hfixed : C.reachOp goal hr v = v)
    (hlb : ∀ b, C.reachOp goal hr b ≤ b → v ≤ b) :
    (C.reachOp goal hr).lfp = v :=
  OrderHom.lfp_eq_of_certificate (C.reachOp goal hr) v hfixed hlb
end Csg.CSG
