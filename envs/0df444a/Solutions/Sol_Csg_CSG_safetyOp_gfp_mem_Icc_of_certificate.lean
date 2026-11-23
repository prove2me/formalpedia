-- Prove2me | solution 1 for Csg.CSG.safetyOp_gfp_mem_Icc_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:25:06.794968+00:00
-- url     : https://prove2.me/submissions/64703874-abbf-4fc7-9463-f27142c1f8c3

import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_SafetyOp
import Definitions.Def_Csg_IntervalCertificate
import Theorems.Thm_OrderHom_gfp_mem_Icc_of_certificate

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (safe : S → Prop) [DecidablePred safe]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (lo hi : S → Set.Icc (0 : ℝ) 1)
    (hpost : lo ≤ C.safetyOp safe hr lo) (hub : ∀ b, b ≤ C.safetyOp safe hr b → b ≤ hi) :
    lo ≤ (C.safetyOp safe hr).gfp ∧ (C.safetyOp safe hr).gfp ≤ hi :=
  OrderHom.gfp_mem_Icc_of_certificate (C.safetyOp safe hr) lo hi hpost hub
end Csg.CSG
