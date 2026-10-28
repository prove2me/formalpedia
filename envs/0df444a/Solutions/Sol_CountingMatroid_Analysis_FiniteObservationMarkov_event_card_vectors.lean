-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteObservationMarkov.event_card_vectors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:05:02.677525+00:00
-- url     : https://prove2.me/submissions/4abcca91-7a14-4c4c-872f-e97e73db2911

import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteObservationMarkov

open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: Uniform length-t tape events have the same cardinality when
represented by fixed-length vectors, enabling finite-sum moment arguments.
TEXLINE: main.tex:1392-1421 -/
theorem solution (t : ℕ) (bad : List Bool → Prop) :
    letI := Classical.propDecidable
    Set.ncard {bits : List Bool | bits.length = t ∧ bad bits} =
      (Finset.univ.filter (fun bits : List.Vector Bool t => bad bits.val)).card := by
  classical
  let S := {bits : List Bool // bits.length = t ∧ bad bits}
  let T := {bits : List.Vector Bool t // bad bits.val}
  let join : T → S := fun bits => ⟨bits.val.val, bits.val.property, bits.property⟩
  have hj : Function.Bijective join := by
    constructor
    · intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : S => x.val) he
    · intro bits
      exact ⟨⟨⟨bits.val, bits.property.1⟩, bits.property.2⟩, rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective join hj)
  change Nat.card S = _
  rw [← hcard]
  change Nat.card {bits : List.Vector Bool t // bad bits.val} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
