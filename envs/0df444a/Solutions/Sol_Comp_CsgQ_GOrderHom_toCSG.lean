-- Prove2me | solution 1 for Comp.CsgQ.GOrderHom_toCSG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:29:01.889207+00:00
-- url     : https://prove2.me/submissions/5281470c-9caf-45dc-8d33-bb42504f204d

import Definitions.Def_Comp_Basic
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Qualitative
import Theorems.Thm_Comp_CsgQ_Pre1_toCSG

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (safe x : Set S) :
    (G.toCSG h).GOrderHom safe x = G.GStepQ safe x := by
  change (G.toCSG h).Pre1 x ∩ safe = G.Pre1Q x ∩ safe
  rw [Pre1_toCSG G h x]
end Comp.CsgQ
