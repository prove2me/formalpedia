-- Prove2me | solution 1 for CCS.projR_union
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:21:20.538034+00:00
-- url     : https://prove2.me/submissions/1e0b2d04-45a6-4a9b-9bfd-7eb653413431

import Definitions.Def_EventStructures_General_Stable
import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_CCS_Syntax
import Definitions.Def_EventStructures_CCS_Par

set_option autoImplicit true
open GES
open CCS
variable {Name : Type*}
variable {E F : SES (Action Name)}
namespace CCS
theorem _root_.solution (C D : Set (Tag E F)) : projR (C ∪ D) = projR C ∪ projR D := by
  ext f
  constructor
  · rintro ⟨t, ht | ht, he⟩
    · exact Or.inl ⟨t, ht, he⟩
    · exact Or.inr ⟨t, ht, he⟩
  · rintro (⟨t, ht, he⟩ | ⟨t, ht, he⟩)
    · exact ⟨t, Or.inl ht, he⟩
    · exact ⟨t, Or.inr ht, he⟩
end CCS
