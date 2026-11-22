-- Prove2me | solution 1 for Comp.CsgQ.Pre1_toCSG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:26:59.258899+00:00
-- url     : https://prove2.me/submissions/6560304f-9025-4f57-91a3-bb64b46b5adc

import Definitions.Def_Comp_Basic
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Qualitative
import Theorems.Thm_Comp_CsgQ_toPMF_support

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (x : Set S) :
    (G.toCSG h).Pre1 x = G.Pre1Q x := by
  ext s
  have hsup : ∀ a1 a2, ((G.toCSG h).K s a1 a2).support = G.supportQ s a1 a2 := fun a1 a2 =>
    toPMF_support G h s a1 a2
  simp only [CSG.Pre1, Pre1Q, Set.mem_setOf_eq, hsup]
end Comp.CsgQ
