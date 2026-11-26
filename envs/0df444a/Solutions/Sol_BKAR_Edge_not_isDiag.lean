-- Prove2me | solution 1 for BKAR.Edge.not_isDiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:32.442668+00:00
-- url     : https://prove2.me/submissions/1cdb1f44-32e9-4efe-b8b8-0a61eb107e2a

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
theorem _root_.solution (e : Edge V) : ¬ e.val.IsDiag :=
  e.property
end BKAR.Edge
