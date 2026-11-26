-- Prove2me | solution 1 for BKAR.Forest.empty_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:42.807852+00:00
-- url     : https://prove2.me/submissions/c42b6da2-2aa6-409a-ac1b-1068b0b235f6

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution :
    (empty V).support = ⟨∅, ⟨emptyAcyclicEdgeSetData⟩⟩ := by
  rfl
end BKAR.Forest
