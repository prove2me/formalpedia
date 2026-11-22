-- Prove2me | solution 1 for Comp.CsgQ.LF_le_of_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:07:18.316306+00:00
-- url     : https://prove2.me/submissions/9666ee42-bc02-4332-89b1-2d99952c9303

import Definitions.Def_Comp_QualitativeLimitFinset
import Definitions.Def_Comp_QualitativeLimitReach
import Theorems.Thm_OrderHom_gfp_le_of_step


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (b y c : Finset S)
    (hinner : ((G.toCSG h).LFInner ↑b ↑y).lfp = (↑c : Set S))
    (hy : (G.toCSG h).LF ↑b ≤ (↑y : Set S)) :
    (G.toCSG h).LF ↑b ≤ (↑c : Set S) := by
  have hLF : (G.toCSG h).LF (↑b : Set S) = ((G.toCSG h).LFOuter ↑b).gfp := rfl
  have hstep : (↑c : Set S) = (G.toCSG h).LFOuter (↑b : Set S) ↑y := hinner.symm
  rw [hLF] at hy ⊢
  exact OrderHom.gfp_le_of_step _ hy hstep
end Comp.CsgQ
