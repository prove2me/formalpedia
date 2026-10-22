-- Prove2me | solution 1 for GOSNIZK.CircuitSound.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:27:54.451028+00:00
-- url     : https://prove2.me/submissions/c7a04f4f-06ca-4854-a8b7-1b9ed49ea6d0

import Mathlib
import Definitions.Def_GOSNIZK_CircuitSound_Scheme

set_option autoImplicit false
open GOSNIZK.CircuitSound

theorem solution (N : ℕ) (b₀ b₁ b₂ : Bool) :
    (4 ≤ N →
      (b₂ = !(b₀ && b₁) ↔
        (ofBit b₀ + ofBit b₁ + 2 * ofBit b₂ - 2 : ZMod N) ∈ ({0, 1} : Set (ZMod N)))) ∧
    (N = 3 →
      (b₂ = !(b₀ && b₁) ↔
        (ofBit b₀ + ofBit b₁ + 2 * ofBit b₂ - 2 : ZMod N) ∈ ({0, 1} : Set (ZMod N)) ∧
        (ofBit b₀ + ofBit b₁ + ofBit b₂ - 1 : ZMod N) ∈ ({0, 1} : Set (ZMod N)))) := by
  constructor
  · intro hN
    have h1 : (1 : ZMod N) ≠ 0 := by
      have := (ZMod.natCast_eq_zero_iff 1 N).not.mpr (by
        intro h; have := Nat.le_of_dvd one_pos h; omega)
      simpa using this
    have h2 : (2 : ZMod N) ≠ 0 := by
      have := (ZMod.natCast_eq_zero_iff 2 N).not.mpr (by
        intro h; have := Nat.le_of_dvd two_pos h; omega)
      simpa using this
    have h3 : (3 : ZMod N) ≠ 0 := by
      have := (ZMod.natCast_eq_zero_iff 3 N).not.mpr (by
        intro h; have := Nat.le_of_dvd (by norm_num) h; omega)
      simpa using this
    have hneg1 : (-1 : ZMod N) ≠ 1 := by
      intro h; apply h2; linear_combination (-1 : ZMod N) * h
    have hneg2 : (-2 : ZMod N) ≠ 1 := by
      intro h; apply h3; linear_combination (-1 : ZMod N) * h
    have h21 : (2 : ZMod N) ≠ 1 := by
      intro h; apply h1; linear_combination h
    have hm1 : (-1 : ZMod N) ≠ 0 := by simpa using h1
    have hm2 : (-2 : ZMod N) ≠ 0 := by simpa using h2
    cases b₀ <;> cases b₁ <;> cases b₂ <;> simp [ofBit, Set.mem_insert_iff] <;>
      first
        | exact ⟨h2, hneg2⟩
        | exact ⟨fun h => hm1 (by linear_combination h), h2⟩
        | (left; ring)
        | exact ⟨fun h => h2 (by linear_combination h), h1⟩
  · intro hN
    subst hN
    cases b₀ <;> cases b₁ <;> cases b₂ <;> decide
