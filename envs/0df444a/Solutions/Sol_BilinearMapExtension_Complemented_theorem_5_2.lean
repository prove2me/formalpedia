-- Prove2me | solution 1 for BilinearMapExtension.Complemented.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:00:52.282984+00:00
-- url     : https://prove2.me/submissions/dea80914-ea62-4f7f-9e84-bee31da39fc3

import Mathlib
import Definitions.Def_BilinearMapExtension_Complemented_Setting
import Theorems.Thm_BilinearMapExtension_Complemented_proposition_4_1
import Theorems.Thm_BilinearMapExtension_Complemented_linear_extension_of_bilinear_extension
import Theorems.Thm_BilinearMapExtension_Complemented_complemented_closure_of_linear_extension
import Theorems.Thm_BilinearMapExtension_Complemented_extension_to_closures
import Theorems.Thm_BilinearMapExtension_Complemented_extension_via_projections

universe u

open BilinearMapExtension.Complemented


/-- Theorem 5.2, p. 5. -/
theorem solution {𝕜 : Type*} [RCLike 𝕜] {X Y : Type u}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (M : Submodule 𝕜 X) (N : Submodule 𝕜 Y) :
    -- (a), for nonzero  and  (the opening line of the proof)
    (M ≠ ⊥ → N ≠ ⊥ →
      ((∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
          (φ : M →L[𝕜] N →L[𝕜] Z), ∃ φh : X →L[𝕜] Y →L[𝕜] Z, IsBilinExtension M N φ φh) ↔
        (IsComplementedSubspace M.topologicalClosure ∧
          IsComplementedSubspace N.topologicalClosure))) ∧
    -- (b)
    (∀ (E : X →L[𝕜] X) (P : Y →L[𝕜] Y),
      IsProjectionOnto E M.topologicalClosure → IsProjectionOnto P N.topologicalClosure →
      ‖E‖ = 1 → ‖P‖ = 1 →
      ∀ (Z : Type u) [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] [CompleteSpace Z]
        (φ : M →L[𝕜] N →L[𝕜] Z),
        ∃ φh : X →L[𝕜] Y →L[𝕜] Z, IsBilinExtension M N φ φh ∧ ‖φh‖ = ‖φ‖) := by
  constructor
  · intro hM hN
    constructor
    · intro hall
      constructor
      · apply complemented_closure_of_linear_extension M
        intro Z _ _ _ T _
        exact (linear_extension_of_bilinear_extension M N (hall Z)).1 hN T
      · apply complemented_closure_of_linear_extension N
        intro Z _ _ _ T _
        exact (linear_extension_of_bilinear_extension M N (hall Z)).2 hM T
    · rintro ⟨hM, hN⟩ Z _ _ _ φ
      obtain ⟨E, hE⟩ :=
        (proposition_4_1 M.topologicalClosure M.isClosed_topologicalClosure).2 hM
      obtain ⟨P, hP⟩ :=
        (proposition_4_1 N.topologicalClosure N.isClosed_topologicalClosure).2 hN
      obtain ⟨φt, hφt, _⟩ := extension_to_closures M N φ
      obtain ⟨φh, _, hext, _, _⟩ := extension_via_projections M N E P hE hP φ φt hφt
      exact ⟨φh, hext⟩
  · intro E P hE hP hnE hnP Z _ _ _ φ
    obtain ⟨φt, hφt, hnorm⟩ := extension_to_closures M N φ
    obtain ⟨φh, _, hext, hlo, hhi⟩ := extension_via_projections M N E P hE hP φ φt hφt
    refine ⟨φh, hext, le_antisymm ?_ hlo⟩
    simpa [hnorm, hnE, hnP] using hhi

