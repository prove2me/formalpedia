-- Prove2me | solution 1 for ConfFamily.inter_diff_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:41:28.339273+00:00
-- url     : https://prove2.me/submissions/61386991-5847-43a9-8b86-39f679ed3250

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
import Theorems.Thm_Bisimilar_symm
import Theorems.Thm_ConfFamily_Indep_symm


set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}
namespace ConfFamily
theorem _root_.solution {c : Set F.Event} {e₁ e₂ : F.Event}
    (he₂ : e₂ ∈ c) (hne : e₁ ≠ e₂) :
    ((c \ {e₁}) ∩ (c \ {e₂})) ∪ {e₂} = c \ {e₁} := by
  ext x
  constructor
  · rintro (⟨hx, -⟩ | hx)
    · exact hx
    · exact (Set.mem_singleton_iff.mp hx) ▸ ⟨he₂, fun h => hne (Set.mem_singleton_iff.mp h).symm⟩
  · rintro ⟨hx, hx₁⟩
    by_cases hxe : x = e₂
    · exact Or.inr (Set.mem_singleton_iff.mpr hxe)
    · exact Or.inl ⟨⟨hx, hx₁⟩, ⟨hx, fun h => hxe (Set.mem_singleton_iff.mp h)⟩⟩
end ConfFamily
