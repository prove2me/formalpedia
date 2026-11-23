-- Prove2me | solution 1 for Csg.CSG.coBuchiInnerOpFun_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:59:03.759867+00:00
-- url     : https://prove2.me/submissions/cfbebc22-3e74-4671-aca6-8f5e2f31f398

import Definitions.Def_Csg_BuchiOp
import Definitions.Def_Csg_CoBuchiOp

set_option autoImplicit true
open Csg
open Csg.CSG
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (U : S → Prop) [DecidablePred U]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) (x y : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (C.coBuchiInnerOpFun U hr x y s : ℝ) = if U s then C.stageValue s (fun s' => (y s' : ℝ))
      else C.stageValue s (fun s' => (x s' : ℝ)) := by
  unfold coBuchiInnerOpFun
  split_ifs <;> rfl
end Csg.CSG
