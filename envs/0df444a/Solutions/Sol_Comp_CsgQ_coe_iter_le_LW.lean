-- Prove2me | solution 1 for Comp.CsgQ.coe_iter_le_LW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:31:59.471007+00:00
-- url     : https://prove2.me/submissions/af04caf4-14dc-4ab7-950d-d2c6cdc8a963

import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_Reach
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Comp_QualitativeLimitFinset
import Theorems.Thm_Comp_CsgQ_coe_lStepF
import Theorems.Thm_Comp_CsgQ_le_lfp_of_step
import Theorems.Thm_OrderHom_le_lfp_of_step


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) (s : S) (n : ℕ) :
    (↑((G.lStepF x y s)^[n] ∅) : Set A1) ≤ (G.toCSG h).LW ↑x ↑y s := by
  have hLW : (G.toCSG h).LW (↑x : Set S) ↑y s = ((G.toCSG h).LStep ↑x ↑y s).lfp := rfl
  rw [hLW]
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_empty]
      exact bot_le
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine OrderHom.le_lfp_of_step _ ih ?_
      rw [coe_lStepF]
end Comp.CsgQ
