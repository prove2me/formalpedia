-- Prove2me | solution 1 for BKAR.AcyclicEdgeSetData.inSameComponent_iff_exists_isSimplePath
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:02:22.928364+00:00
-- url     : https://prove2.me/submissions/d8d016d5-496d-418f-a409-8ba7acc550a2

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest

set_option autoImplicit false
open BKAR
open BKAR.AcyclicEdgeSetData
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.AcyclicEdgeSetData
theorem _root_.solution
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {i j : V} :
    data.inSameComponent i j ↔
      ∃ γ : List (Edge V), EdgePath.IsSimplePath S γ i j := by
  constructor
  · intro h
    exact ⟨data.pathIn i j h,
      data.isSimplePath_iff.mp (data.pathIn_isSimple h)⟩
  · rintro ⟨γ, hγ⟩
    exact data.sameComponent_of_simplePath
      (data.isSimplePath_iff.mpr hγ)
end BKAR.AcyclicEdgeSetData
