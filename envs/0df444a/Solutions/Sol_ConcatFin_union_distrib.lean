-- Prove2me | solution 1 for ConcatFin_union_distrib
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:33:45.19881+00:00
-- url     : https://prove2.me/submissions/5e14dd5b-7e75-4826-9996-1212c4a2a477

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L0 L1 L2 : Set (List A)} :
    L0 * (L1 ∪ L2) = L0 * L1 ∪ L0 * L2 := by
  ext al ; constructor
  · rintro ⟨al0, alu, h_al0, (h_al1 | h_al2), h_al⟩
    · left ; use al0, alu
    · right ; use al0, alu
  · rintro (⟨al0, al1, h_al0, h_al1, h_al⟩ | ⟨al0, al2, h_al0, h_al2, h_al⟩)
    · use al0, al1 ; tauto
    · use al0, al2 ; tauto
