-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.admissible_in_truncation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:44:35.144449+00:00
-- url     : https://prove2.me/submissions/a88cfea7-195b-4e71-ba7c-9b39ae2c8827

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutAdm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution : AdmInCut := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG v a ha x hx
  obtain ⟨w, rfl⟩ := ha
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have h1 := w.2.1.1 v j hj
  have hnode := (hG v).2.2.2.2.2
  have hcut : ∀ Y ∈ (S.G.place (S.pl v)).cutI S.l, Y ∈ Set.Icc (S.cutLo v) (S.cutHi v) := by
    intro Y hY
    simp only [Sz.Cfg.cutI, Set.mem_setOf_eq] at hY
    simp only [C.HidaSetting.cutLo, C.HidaSetting.cutHi, Set.mem_Icc]
    constructor <;> linarith [hY.1, hY.2]
  by_cases hp : ((w.1 v)[j]'hj).1
  · rw [if_pos hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    exact hcut _ (hnode _ hy).1
  · rw [if_neg hp] at h1
    have hy : (∃ b, ((w.1 v)[j]'hj).2 - 1 ∈ S.grid v b) ∨ ((w.1 v)[j]'hj).2 - 1 ∈ S.grid1 v := by
      rcases Finset.mem_union.1 h1 with h | h
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr h
    have := hcut _ (hnode _ hy).2.1
    simpa using this
end Formalism.FourierDecayAlt.P.CutMP
