-- Prove2me | solution 1 for ConcatInf_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:34:04.326594+00:00
-- url     : https://prove2.me/submissions/7b17c3fe-06e9-447a-a914-a792e7ff32b3

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L0 L0' : Set (List A)} {L1 L1' : Set (Stream' A)}
    (h0 : L0 ⊆ L0') (h1 : L1 ⊆ L1') :
    L0 * L1 ⊆ L0' * L1' := by
  rintro as ⟨al0, as0, h_al0, h_as0, rfl⟩
  use al0, as0 ; grind
