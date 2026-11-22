-- Prove2me | solution 1 for ConfFamily.config_diff_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:03:26.419801+00:00
-- url     : https://prove2.me/submissions/45608e10-9a76-4143-a758-69aeda33ba29

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}
namespace ConfFamily
theorem _root_.solution (hF : Stable F) {c : Set F.Event} {e₁ e₂ : F.Event}
    (h₁ : F.Config (c \ {e₁})) (h₂ : F.Config (c \ {e₂})) (hc : F.Config c) :
    F.Config ((c \ {e₁}) ∩ (c \ {e₂})) := by
  have hpair : ((c \ {e₁}) ∩ (c \ {e₂})) = ⋂₀ {c \ {e₁}, c \ {e₂}} := by
    rw [Set.sInter_pair]
  rw [hpair]
  refine hF ⟨c \ {e₁}, Or.inl rfl⟩ ?_ hc ?_
  · rintro x (rfl | rfl)
    · exact h₁
    · exact h₂
  · rintro x (rfl | rfl) <;> exact fun _ hy => hy.1
end ConfFamily
