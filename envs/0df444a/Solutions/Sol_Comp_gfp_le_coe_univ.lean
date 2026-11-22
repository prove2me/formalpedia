-- Prove2me | solution 1 for Comp.gfp_le_coe_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:27:19.759468+00:00
-- url     : https://prove2.me/submissions/6b1d6e9f-e361-4ef4-9ecf-b6592d5fe43b

import Definitions.Def_Comp_Lattice
import Mathlib.Data.Fintype.Card
import Definitions.Def_Comp_FixLoop

set_option autoImplicit true
open Comp
variable {S : Type*} [DecidableEq S]
variable [Fintype S]
omit [DecidableEq S]
namespace Comp
theorem _root_.solution (F : Set S →o Set S) : F.gfp ≤ (↑(Finset.univ : Finset S) : Set S) := by
  rw [Finset.coe_univ]
  exact le_top
end Comp
