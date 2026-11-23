-- Prove2me | solution 1 for Comp.CsgQ.G_eq_coe_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:04:47.896625+00:00
-- url     : https://prove2.me/submissions/7c998352-9761-4c16-b8fd-9b138580d1dc

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
import Theorems.Thm_Comp_CsgQ_coe_gStepF
import Theorems.Thm_Comp_CsgQ_G_le_coe_iter
import Theorems.Thm_Comp_CsgQ_GOrderHom_toCSG
import Theorems.Thm_OrderHom_eq_gfp_of_fixed_of_ge


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (safe c : Finset S) (n : ℕ)
    (hiter : (G.gStepF safe)^[n] Finset.univ = c) (hfix : G.gStepF safe c = c) :
    (G.toCSG h).G (↑safe : Set S) = ↑c := by
  have hG : (G.toCSG h).G (↑safe : Set S) = ((G.toCSG h).GOrderHom ↑safe).gfp := rfl
  have hfixS : (G.toCSG h).GOrderHom (↑safe : Set S) ↑c = (↑c : Set S) := by
    rw [GOrderHom_toCSG, ← coe_gStepF, hfix]
  have hge := G_le_coe_iter G h safe n
  rw [hiter, hG] at hge
  rw [hG]
  exact (OrderHom.eq_gfp_of_fixed_of_ge _ hfixS hge).symm
end Comp.CsgQ
