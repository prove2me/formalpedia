-- Prove2me | solution 1 for Comp.CsgQ.AF_le_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:00:21.51291+00:00
-- url     : https://prove2.me/submissions/5d22ec8d-a8b0-4b6a-9143-d5e39fcad3cc

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeAlmostFinset
import Theorems.Thm_OrderHom_gfp_le_of_step


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S)
    (hinner : ((G.toCSG h).AFInner ↑b ↑y).lfp = (↑c : Set S))
    (hy : (G.toCSG h).AF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).AF ↑b ≤ (↑c : Set S) := by
  have hAF : (G.toCSG h).AF (↑b : Set S) = ((G.toCSG h).AFOuter ↑b).gfp := rfl
  have hstep : (↑c : Set S) = (G.toCSG h).AFOuter (↑b : Set S) ↑y := hinner.symm
  rw [hAF] at hy ⊢
  exact OrderHom.gfp_le_of_step _ hy hstep
end Comp.CsgQ
