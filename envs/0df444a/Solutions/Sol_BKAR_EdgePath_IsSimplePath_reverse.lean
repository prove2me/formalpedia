-- Prove2me | solution 1 for BKAR.EdgePath.IsSimplePath.reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:54.334313+00:00
-- url     : https://prove2.me/submissions/d2cc8122-9ed3-45ea-9530-df383172a8fd

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.EdgePath
variable {V} [DecidableEq V]
open BKAR.EdgePath.IsSimplePath
namespace BKAR.EdgePath.IsSimplePath
theorem _root_.solution {S : Finset (Edge V)}
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j) :
    IsSimplePath S γ.reverse j i :=
  ⟨h.1.reverse, List.nodup_reverse.mpr h.2⟩
end BKAR.EdgePath.IsSimplePath
