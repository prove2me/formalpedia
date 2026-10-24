-- Prove2me | solution 1 for BilinearMapExtension.Complemented.complemented_closure_of_linear_extension
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T06:52:49.515552+00:00
-- url     : https://prove2.me/submissions/64f39d3a-9fe4-445d-88bc-524c406fc4f9

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting

universe u

open BilinearMapExtension.Complemented

/-- Extend the inclusion into the closure, then use continuity to obtain a projection. -/
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X] (M : Submodule 𝕜 X)
    (h : ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
      (T : M →L[𝕜] Z), T ≠ 0 → ∃ Th : X →L[𝕜] Z, ∀ u : M, Th u = T u) :
    IsComplementedSubspace M.topologicalClosure := by
  let T : M →L[𝕜] M.topologicalClosure :=
    M.subtypeL.codRestrict M.topologicalClosure (fun x => M.le_topologicalClosure x.property)
  have hex : ∃ Th : X →L[𝕜] M.topologicalClosure, ∀ u : M, Th u = T u := by
    by_cases hT : T = 0
    · exact ⟨0, fun u => by simp [hT]⟩
    · exact h M.topologicalClosure T hT
  obtain ⟨Th, hTh⟩ := hex
  let E : X →L[𝕜] X := M.topologicalClosure.subtypeL.comp Th
  have heq : Set.EqOn E (ContinuousLinearMap.id 𝕜 X) (M : Set X) := by
    intro x hx
    exact congrArg Subtype.val (hTh ⟨x, hx⟩)
  have hfix : ∀ x : M.topologicalClosure, Th x = x := by
    intro x
    apply Subtype.ext
    exact heq.closure E.continuous (ContinuousLinearMap.id 𝕜 X).continuous x.property
  exact ⟨M.isClosed_topologicalClosure, Th.ker, Th.isClosed_ker,
    (ContinuousLinearMap.isTopCompl_of_proj hfix).isCompl⟩
