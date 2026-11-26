-- Prove2me | solution 1 for BKAR.EdgePath.IsSimplePath.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:51.910801+00:00
-- url     : https://prove2.me/submissions/72b7dc86-42e7-4b17-8f75-87169f5eae79

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_EdgePath_IsPath_mono

set_option autoImplicit false
open BKAR
open BKAR.EdgePath
variable {V} [DecidableEq V]
open BKAR.EdgePath.IsSimplePath
namespace BKAR.EdgePath.IsSimplePath
theorem _root_.solution {S T : Finset (Edge V)} (hsub : S ⊆ T)
    {γ : List (Edge V)} {i j : V}
    (h : IsSimplePath S γ i j) :
    IsSimplePath T γ i j :=
  ⟨h.1.mono hsub, h.2⟩
end BKAR.EdgePath.IsSimplePath
