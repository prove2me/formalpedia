-- Prove2me | solution 1 for BKAR.AcyclicEdgeSetData.not_isAcyclicEdgeSet_insert_of_inSameComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:03:55.764625+00:00
-- url     : https://prove2.me/submissions/a21a8ceb-0cd6-47fc-b01f-8787eae3601e

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Sym.Sym2
import Definitions.Def_BKAR_Forest
import Theorems.Thm_BKAR_EdgePath_IsPath_mono
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono
import Theorems.Thm_BKAR_IsAcyclicEdgeSet_mono

set_option autoImplicit false
open BKAR
open BKAR.AcyclicEdgeSetData
variable {V} [Fintype V] [DecidableEq V]
namespace BKAR.AcyclicEdgeSetData
theorem _root_.solution
    {S : Finset (Edge V)} (data : AcyclicEdgeSetData S)
    {e : Edge V} (heS : e ∉ S)
    (hcomp : data.inSameComponent e.left e.right) :
    ¬ IsAcyclicEdgeSet (insert e S) := by
  rintro ⟨insertData⟩
  let γ := data.pathIn e.left e.right hcomp
  have hγData : data.isSimplePath γ e.left e.right :=
    data.pathIn_isSimple hcomp
  have hγGraphS : EdgePath.IsSimplePath S γ e.left e.right :=
    data.isSimplePath_iff.mp hγData
  have hγGraphInsert : EdgePath.IsSimplePath (insert e S) γ e.left e.right :=
    hγGraphS.mono (by
      intro e' he'
      exact Finset.mem_insert_of_mem he')
  have hγInsert : insertData.isSimplePath γ e.left e.right :=
    insertData.isSimplePath_iff.mpr hγGraphInsert
  have hsingle : insertData.isSimplePath [e] e.left e.right :=
    insertData.edge_isSimplePath (Finset.mem_insert_self e S)
  have heq : γ = [e] :=
    insertData.path_unique hγInsert hsingle
  have he_mem_γ : e ∈ γ := by
    rw [heq]
    simp
  have he_mem_S : e ∈ S :=
    hγGraphS.edge_mem e he_mem_γ
  exact heS he_mem_S
end BKAR.AcyclicEdgeSetData
