-- Prove2me | solution 1 for BKAR.Forest.acyclic_insert_iff_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:22:43.282122+00:00
-- url     : https://prove2.me/submissions/988d1f33-fb8d-4226-83c9-820188e8e2d9

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Edge_left_ne_right
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_acyclic_insert_iff
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same


attribute [local simp] BKAR.Forest.emptyActiveEdge_val

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (F : Forest V) {e : Edge V}
    (he : e ∉ F.edges) :
    IsAcyclicEdgeSet (insert e F.edges) ↔
      ¬ F.inSameComponent e.left e.right := by
  have hmk : Edge.mk e.left e.right e.left_ne_right = e := by
    apply Subtype.ext
    rw [Edge.mk_val, e.mk_left_right_eq]
  have hnotmk : Edge.mk e.left e.right e.left_ne_right ∉ F.edges := by
    rw [hmk]
    exact he
  simpa [hmk] using F.acyclic_insert_iff e.left_ne_right hnotmk
end BKAR.Forest
