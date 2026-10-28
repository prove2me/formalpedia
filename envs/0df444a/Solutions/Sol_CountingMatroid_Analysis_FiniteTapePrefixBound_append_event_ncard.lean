-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteTapePrefixBound.append_event_ncard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:25:17.778336+00:00
-- url     : https://prove2.me/submissions/48539bc1-6493-465a-be14-430b4b6cc758

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

/-!
Finite fair-bit conditioning by a consumed prefix. Appending a fixed prefix
is a bijection on its suffix event; disjoint consumed-prefix cylinders let
uniform suffix estimates transfer to the whole finite tape. This module
proves only counting facts, not the program's stopping-prefix property or
the phase's conditional analytic estimate.
-/

namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteTapePrefixBound

/-- INTERNAL: Deleting a fixed consumed prefix bijects its tape event with
an event on all remaining suffixes. No condition on the suffix event is needed.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem solution (m : ℕ) (pref : List Bool)
    (hlen : pref.length ≤ m) (E : List Bool → Prop) :
    Set.ncard {bits : List Bool | bits.length = m ∧ pref <+: bits ∧ E bits} =
      Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
        E (pref ++ suffix)} := by
  rw [← Set.ncard_image_of_injective
    {suffix : List Bool | suffix.length = m - pref.length ∧ E (pref ++ suffix)}
    (List.append_right_injective pref)]
  congr 1
  ext bits
  constructor
  · rintro ⟨hb, hp, he⟩
    refine ⟨bits.drop pref.length, ⟨?_, ?_⟩, ?_⟩
    · simp only [List.length_drop, hb]
    · simpa only [← List.prefix_append_drop hp] using he
    · exact (List.prefix_append_drop hp).symm
  · rintro ⟨suffix, ⟨hs, he⟩, rfl⟩
    refine ⟨?_, List.prefix_append pref suffix, he⟩
    simp only [List.length_append, hs, Nat.add_sub_of_le hlen]
