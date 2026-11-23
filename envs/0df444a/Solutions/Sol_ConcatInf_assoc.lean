-- Prove2me | solution 1 for ConcatInf_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:53:02.92459+00:00
-- url     : https://prove2.me/submissions/3339c712-e5ce-46bc-ab0e-2ae375a7975f

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L0 L0' : Set (List A)} {L1 : Set (Stream' A)} :
    (L0 * L0') * L1 = L0 * (L0' * L1) := by
  ext as ; constructor
  · rintro ⟨al, as1, ⟨al0, al0', h_al0, h_al0', rfl⟩, h_as1, rfl⟩
    use al0, (al0' ++ₛ as1) ; simp [h_al0, append_append_stream] ; use al0', as1
  · rintro ⟨al0, as', h_al0, ⟨al0', as1, h_al0', h_as1, rfl⟩, rfl⟩
    rw [← append_append_stream]
    use (al0 ++ al0'), as1 ; simp [h_as1] ; use al0, al0'
