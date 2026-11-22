-- Prove2me | solution 1 for CCS.projR_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:22.485311+00:00
-- url     : https://prove2.me/submissions/03fe9d56-6231-4b42-8da6-3b65c1b73380

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par
import Theorems.Thm_ConfFamily_Indep_symm


set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
variable {c : Set (Tag E F)}
namespace CCS
theorem _root_.solution {t : Tag E F} {y : F.Event} (hy : t.evR = some y) :
    projR (c ∪ {t}) = projR c ∪ {y} := by
  ext f
  constructor
  · rintro ⟨u, hu | hu, he⟩
    · exact Or.inl ⟨u, hu, he⟩
    · replace hu : u = t := hu
      subst hu
      rw [hy] at he
      exact Or.inr (Option.some.inj he).symm
  · rintro (⟨u, hu, he⟩ | he)
    · exact ⟨u, Or.inl hu, he⟩
    · replace he : f = y := he
      exact ⟨t, Or.inr rfl, by rw [hy, he]⟩
end CCS
