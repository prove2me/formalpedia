-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.words_pos_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:58:21.074929+00:00
-- url     : https://prove2.me/submissions/d0f37f7c-b7b2-4439-8e27-e2421455382b

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
open scoped ComplexOrder
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C.WordsPosOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG Kr hK0 Th e w
  show 0 < Word.size S.P w.1
  unfold Word.size
  apply Finset.prod_pos
  intro v _
  apply List.prod_pos
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨a, ha, rfl⟩ := hx
  apply abs_pos.mpr
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
  have hadm := w.2.1.1 v j hj
  by_cases hb : ((w.1 v)[j]'hj).1 = true
  · rw [if_pos hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact ((hG v).2.2.2.2.2 _ hy).2.2.1
  · rw [if_neg hb] at hadm
    have hy : (∃ a, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v a) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.mp hadm with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := ((hG v).2.2.2.2.2 _ hy).2.2.2
    rwa [sub_add_cancel] at this
end Formalism.FourierDecayAlt.P
