-- Prove2me | solution 1 for CountingMatroid.Bridge.list_tape_event_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:18:05.47398+00:00
-- url     : https://prove2.me/submissions/a6daf9f4-dd79-4bc6-89cb-79530b896ecb

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge

/-- Convert an event on lists of exactly K bits to the same event on Fin K tapes. -/
theorem solution (K : ℕ) (event : List Bool → Prop) :
    Set.ncard {xs : List Bool | xs.length = K ∧ event xs} =
      Nat.card {bits : Fin K → Bool // event (List.ofFn bits)} := by
  classical
  symm
  apply Nat.card_congr
  apply Equiv.ofBijective (fun f : {bits : Fin K → Bool // event (List.ofFn bits)} =>
    (⟨List.ofFn f.val, by simp [f.property]⟩ :
      {xs : List Bool // xs.length = K ∧ event xs}))
  constructor
  · intro a b h
    apply Subtype.ext
    exact List.ofFn_injective (congrArg Subtype.val h)
  · rintro ⟨xs, hlen, hevent⟩
    subst K
    refine ⟨⟨xs.get, by simpa only [List.ofFn_get] using hevent⟩, ?_⟩
    apply Subtype.ext
    exact List.ofFn_get xs
