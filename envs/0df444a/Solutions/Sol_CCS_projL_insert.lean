-- Prove2me | solution 1 for CCS.projL_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:21.730425+00:00
-- url     : https://prove2.me/submissions/fdbe9c0a-fb97-4ade-acbe-8bb9c7a0ef26

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
theorem _root_.solution {t : Tag E F} {x : E.Event} (hx : t.evL = some x) :
    projL (c ∪ {t}) = projL c ∪ {x} := by
  ext e
  constructor
  · rintro ⟨u, hu | hu, he⟩
    · exact Or.inl ⟨u, hu, he⟩
    · replace hu : u = t := hu
      subst hu
      rw [hx] at he
      exact Or.inr (Option.some.inj he).symm
  · rintro (⟨u, hu, he⟩ | he)
    · exact ⟨u, Or.inl hu, he⟩
    · replace he : e = x := he
      exact ⟨t, Or.inr rfl, by rw [hx, he]⟩
end CCS
