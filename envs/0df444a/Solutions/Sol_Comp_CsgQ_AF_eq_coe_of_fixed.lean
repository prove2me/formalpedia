-- Prove2me | solution 1 for Comp.CsgQ.AF_eq_coe_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:06:49.165908+00:00
-- url     : https://prove2.me/submissions/0b0c6778-db40-49cb-9707-a343d7dc6c30

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Theorems.Thm_OrderHom_eq_gfp_of_fixed_of_ge


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b y : Finset S)
    (hinner : ((G.toCSG h).AFInner ↑b ↑y).lfp = (↑y : Set S))
    (hy : (G.toCSG h).AF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).AF ↑b = (↑y : Set S) := by
  have hAF : (G.toCSG h).AF (↑b : Set S) = ((G.toCSG h).AFOuter ↑b).gfp := rfl
  have hfixS : (G.toCSG h).AFOuter (↑b : Set S) ↑y = (↑y : Set S) := hinner
  rw [hAF] at hy ⊢
  exact (OrderHom.eq_gfp_of_fixed_of_ge _ hfixS hy).symm
end Comp.CsgQ
