-- Prove2me | solution 1 for BKAR.ForestIndex.ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:58.513546+00:00
-- url     : https://prove2.me/submissions/1dcd8c8c-208f-4f4c-9950-00742c4ae391

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.ForestIndex
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.ForestIndex
theorem _root_.solution {I J : ForestIndex V} (h : I.edges = J.edges) : I = J := by
  cases I
  cases J
  cases h
  rfl
end BKAR.ForestIndex
