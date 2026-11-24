-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.valS_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:40:58.721908+00:00
-- url     : https://prove2.me/submissions/b9818b73-fb39-4142-8df2-a3fb2866fc7c

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_lord_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_le_valS_iff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_substS_rename

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] {L : Type} [DecidableEq L] {L' : Type} [DecidableEq L'] {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (f : L → L') (hf : Function.Injective f) (sg' : L' → Bool) (S' : Finset L')
    (F : MvPolynomial (L × Fin r) K) :
    valS sg' S' (rename (Prod.map f id) F) = valS (sg' ∘ f) (S'.preimage f hf.injOn) F := by
  have hinj : Function.Injective (Prod.map f (id : Fin r → Fin r)) :=
    hf.prodMap Function.injective_id
  have key : ∀ n : WithTop ℤ, n ≤ valS sg' S' (rename (Prod.map f id) F) ↔
      n ≤ valS (sg' ∘ f) (S'.preimage f hf.injOn) F := by
    intro n
    rw [le_valS_iff, le_valS_iff, subV, substS_rename _ _ _ f hf]
    constructor
    · intro h β
      have := h (Finsupp.mapDomain (Prod.map f id) β)
      rwa [coeff_rename_mapDomain _ hinj] at this
    · intro h β'
      by_cases hβ : ∃ β, Finsupp.mapDomain (Prod.map f (id : Fin r → Fin r)) β = β'
      · obtain ⟨β, rfl⟩ := hβ
        rw [coeff_rename_mapDomain _ hinj]
        exact h β
      · rw [coeff_rename_eq_zero, lord_zero]
        · exact le_top
        · intro u hu
          exact absurd ⟨u, hu⟩ hβ
  exact le_antisymm ((key _).mp le_rfl) ((key _).mpr le_rfl)
end Formalism.MainNotions.PlaneGram
