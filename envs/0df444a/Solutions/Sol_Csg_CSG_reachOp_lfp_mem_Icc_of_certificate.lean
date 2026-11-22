-- Prove2me | solution 1 for Csg.CSG.reachOp_lfp_mem_Icc_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:27:23.865799+00:00
-- url     : https://prove2.me/submissions/1290e940-0486-4093-8354-286cf9e01c38

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_IntervalCertificate
import Theorems.Thm_OrderHom_lfp_mem_Icc_of_certificate

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (lo hi : S → Set.Icc (0 : ℝ) 1)
    (hlb : ∀ b, C.reachOp goal hr b ≤ b → lo ≤ b) (hpre : C.reachOp goal hr hi ≤ hi) :
    lo ≤ (C.reachOp goal hr).lfp ∧ (C.reachOp goal hr).lfp ≤ hi :=
  OrderHom.lfp_mem_Icc_of_certificate (C.reachOp goal hr) lo hi hlb hpre
end Csg.CSG
