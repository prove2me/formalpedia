-- Prove2me | solution 1 for BKAR.Edge.left_ne_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:38.010071+00:00
-- url     : https://prove2.me/submissions/ee6911f3-d3ff-455e-a2b4-1a9cdce760f0

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.Edge
variable {V} [DecidableEq V]
namespace BKAR.Edge
theorem _root_.solution (e : Edge V) : e.left ≠ e.right := by
  intro h
  exact e.property (by
    rw [← e.mk_left_right_eq]
    exact (Sym2.mk_isDiag_iff).mpr h)
end BKAR.Edge
