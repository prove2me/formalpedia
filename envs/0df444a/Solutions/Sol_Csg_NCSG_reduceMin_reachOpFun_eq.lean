-- Prove2me | solution 1 for Csg.NCSG.reduceMin_reachOpFun_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:06:37.773795+00:00
-- url     : https://prove2.me/submissions/ebf52a63-a74f-4396-952b-c225093578ee

import Definitions.Def_Csg_CoalitionComplement
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_CoalitionComplementReach
import Theorems.Thm_Csg_NCSG_reduceMax_r_zero
import Theorems.Thm_Csg_NCSG_reduceMin_r_zero
import Theorems.Thm_Csg_NCSG_reduceMin_stageValue_eq


set_option autoImplicit true
open Csg
open Csg.NCSG
variable {S Players : Type*} {A : Players → Type*}
  [Fintype S] [Fintype Players] [DecidableEq Players]
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
variable (C : Finset Players) (G : NCSG S Players A)
namespace Csg.NCSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a, G.r s a = 0) (v : S → Set.Icc (0 : ℝ) 1) (s : S) :
    (G.reduceMax Cᶜ).reachOpFun goal (G.reduceMax_r_zero Cᶜ hr) v s =
      (G.reduceMin C).reachOpFun goal (G.reduceMin_r_zero C hr) v s := by
  by_cases h : goal s
  · simp only [CSG.reachOpFun, if_pos h]
  · simp only [CSG.reachOpFun, if_neg h]
    exact Subtype.ext (reduceMin_stageValue_eq C G s (fun s' => (v s' : ℝ)))
end Csg.NCSG
