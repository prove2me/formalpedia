-- Prove2me | solution 1 for Comp.CsgQ.G_le_coe_iter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:02:12.691142+00:00
-- url     : https://prove2.me/submissions/69531753-0d13-4004-ab2d-961dd9e6d54c

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
import Theorems.Thm_Comp_CsgQ_coe_gStepF
import Theorems.Thm_Comp_CsgQ_GOrderHom_toCSG
import Theorems.Thm_OrderHom_gfp_le_of_step


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (safe : Finset S) (n : ℕ) :
    (G.toCSG h).G (↑safe : Set S) ≤ ↑((G.gStepF safe)^[n] Finset.univ) := by
  have hG : (G.toCSG h).G (↑safe : Set S) = ((G.toCSG h).GOrderHom ↑safe).gfp := rfl
  rw [hG]
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, Finset.coe_univ]
      exact le_top
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine OrderHom.gfp_le_of_step _ ih ?_
      rw [GOrderHom_toCSG, coe_gStepF]
end Comp.CsgQ
