-- Prove2me | solution 1 for BKAR.AcyclicEdgeSetData.inSameComponent_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:19.718573+00:00
-- url     : https://prove2.me/submissions/faa8b497-2554-48ea-8bb0-f50522429050

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_AcyclicEdgeSetData_inSameComponent_iff_exists_isSimplePath

set_option autoImplicit false
open BKAR
open BKAR.AcyclicEdgeSetData
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.AcyclicEdgeSetData
theorem _root_.solution
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j : V} (h : data.inSameComponent i j) :
    data.inSameComponent j i := by
  rw [data.inSameComponent_iff_exists_isSimplePath] at h ⊢
  rcases h with ⟨γ, hγ⟩
  exact ⟨γ.reverse, hγ.reverse⟩
end BKAR.AcyclicEdgeSetData
