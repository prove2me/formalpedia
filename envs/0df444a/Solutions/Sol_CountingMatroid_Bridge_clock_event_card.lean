-- Prove2me | solution 1 for CountingMatroid.Bridge.clock_event_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:17:49.917628+00:00
-- url     : https://prove2.me/submissions/33bd91bb-5378-4d14-af07-9973260ae71c

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid.Bridge

namespace CountingMatroid.Bridge

private noncomputable def splitClock {K B : ℕ} (e : Fin K ↪ Fin B) :
    (Fin B → Bool) ≃ (Fin K → Bool) × ({j : Fin B // j ∉ Set.range e} → Bool) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun j => j ∈ Set.range e) (fun _ => Bool)).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective e e.injective).symm
      (Equiv.refl Bool)) (Equiv.refl _))

end CountingMatroid.Bridge

/-- Restricting a uniformly chosen clock tape to any fixed injective set of
coin positions multiplies every event's cardinality by exactly `2^(B-K)`. -/
theorem solution {K B : ℕ} (e : Fin K ↪ Fin B) (event : (Fin K → Bool) → Prop) :
    Nat.card {bits : Fin B → Bool // event (fun i => bits (e i))} =
      Nat.card {bits : Fin K → Bool // event bits} * 2^(B-K) := by
  classical
  let E := splitClock e
  have hE (bits : Fin B → Bool) : (E bits).1 = (fun i => bits (e i)) := rfl
  let E' := (E.subtypeEquiv (p := fun bits => event (fun i => bits (e i)))
    (q := fun pair => event pair.1) (fun _ => Iff.rfl)).trans
      Equiv.prodSubtypeFstEquivSubtypeProd
  rw [Nat.card_congr E', Nat.card_prod]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_subtype_compl, Fintype.card_fin]
  congr 2
  simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofInjective e e.injective).symm
