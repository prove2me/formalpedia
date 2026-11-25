-- Prove2me | solution 1 for ChromaticReconstruction.skeleton_isTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:13:32.118532+00:00
-- url     : https://prove2.me/submissions/6d421179-1d90-40bc-b750-6d507d5d9f68

import Definitions.Def_RequestProject_WeightedIso
import Definitions.Def_RequestProject_ProperTree
import Theorems.Thm_ChromaticReconstruction_exists_not_leaf
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inl_inr
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inl
import Theorems.Thm_ChromaticReconstruction_leafExt_adj_inr_inr
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_reachable_map
import Theorems.Thm_ChromaticReconstruction_theta_mk
attribute [local simp] ChromaticReconstruction.killP1_X_one
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inl_inr
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inl
attribute [local simp] ChromaticReconstruction.leafExt_adj_inr_inr
attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk



set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V] {T : SimpleGraph V}
namespace ChromaticReconstruction
theorem _root_.solution (hT : IsProperTree T) : (skeleton T).IsTree := by
  refine ⟨?_, hT.1.2.induce _⟩
  obtain ⟨v, hv⟩ := exists_not_leaf hT
  haveI : Nonempty (SkelVert T) := ⟨⟨v, hv⟩⟩
  refine ⟨fun c c' => ?_⟩
  let e := properIso hT
  have hr : (leafExt (skeleton T) (leafCount T)).Reachable (.inl c) (.inl c') := by
    have := (hT.1.1.preconnected c.1 c'.1).map e.symm.toHom
    have h1 : e.symm c.1 = .inl c := e.toEquiv.symm_apply_eq.2 rfl
    have h2 : e.symm c'.1 = .inl c' := e.toEquiv.symm_apply_eq.2 rfl
    simpa [h1, h2] using this
  let f : SkelVert T ⊕ (Σ c, Fin (leafCount T c)) → SkelVert T := fun x =>
    match x with
    | .inl i => i
    | .inr l => l.1
  have := reachable_map f (leafExt (skeleton T) (leafCount T)).edgeSet (skeleton T).edgeSet
    (u := .inl c) (v := .inl c')
    (by
      intro u w huw _
      rw [SimpleGraph.mem_edgeSet] at huw
      rcases u with i | l <;> rcases w with j | l'
      · exact Or.inr huw
      · exact Or.inl (leafExt_adj_inl_inr.1 huw).symm
      · exact Or.inl (leafExt_adj_inr_inl.1 huw)
      · exact absurd huw leafExt_adj_inr_inr)
    (by rw [SimpleGraph.fromEdgeSet_edgeSet]; exact hr)
  rw [SimpleGraph.fromEdgeSet_edgeSet] at this
  exact this
end ChromaticReconstruction
