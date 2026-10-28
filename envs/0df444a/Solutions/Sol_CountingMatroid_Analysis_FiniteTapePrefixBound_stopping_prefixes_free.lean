-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteTapePrefixBound.stopping_prefixes_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T11:27:34.642376+00:00
-- url     : https://prove2.me/submissions/5693fcfb-157d-4d00-b5d0-3bcff7ccdb03

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

/-- INTERNAL: Successful stopping histories have prefix-free consumed
prefixes. A cursor beyond the finite block contributes the whole tape, so
this structural fact does not itself require a cursor-coverage bound.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem solution (m : ℕ) (S : Finset (List Bool))
    (cursor : List Bool → ℕ) (hlen : ∀ bits ∈ S, bits.length = m)
    (hreplay : ∀ bitsA ∈ S, ∀ bitsB ∈ S, cursor bitsA ≤ m →
      bitsA.take (cursor bitsA) <+: bitsB → cursor bitsB = cursor bitsA) :
    ∀ a ∈ S.image (fun bits => bits.take (cursor bits)),
      ∀ b ∈ S.image (fun bits => bits.take (cursor bits)), a <+: b → a = b := by
  intro a ha b hb hab
  obtain ⟨bitsA, hmA, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨bitsB, hmB, rfl⟩ := Finset.mem_image.mp hb
  apply hab.eq_of_length
  by_cases hwithin : cursor bitsA ≤ m
  · have hc := hreplay bitsA hmA bitsB hmB hwithin
      (hab.trans (List.take_prefix _ _))
    simp only [List.length_take, hlen bitsA hmA, hlen bitsB hmB, hc]
  · have hle := hab.length_le
    simp only [List.length_take, hlen bitsA hmA, hlen bitsB hmB] at hle ⊢
    omega
