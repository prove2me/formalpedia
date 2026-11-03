-- Prove2me | solution 1 for BitDFT.kunpack_digit_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T22:45:52.35279+00:00
-- url     : https://prove2.me/submissions/9b19284c-e65c-4917-ae9b-d80e809c84c3

import Mathlib

set_option autoImplicit false
noncomputable section

namespace UnpackChunk

/-- The width-`w` block of `X` starting at bit `o`, read as a natural number. -/
def block (X o w : ℕ) : ℕ := X / 2 ^ o % 2 ^ w

theorem block_lt (X o w : ℕ) : block X o w < 2 ^ w := Nat.mod_lt _ (by positivity)

/-- A block is a masked shift. -/
theorem block_eq_land (X o w : ℕ) : block X o w = (X >>> o) &&& (2 ^ w - 1) := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
  rfl

/-- Residue of `W` in `[0, 2^(β r))`, as a natural number. -/
def resid (β r : ℕ) (W : ℤ) : ℕ := (W % (2 : ℤ) ^ (β * r)).toNat

theorem resid_cast (β r : ℕ) (W : ℤ) : (resid β r W : ℤ) = W % (2 : ℤ) ^ (β * r) := by
  have hnn : 0 ≤ W % (2 : ℤ) ^ (β * r) := Int.emod_nonneg _ (by positivity : (0:ℤ) < (2:ℤ)^(β*r)).ne'
  simp only [resid, Int.toNat_of_nonneg hnn]

theorem resid_lt (β r : ℕ) (W : ℤ) : resid β r W < 2 ^ (β * r) := by
  have h : W % (2 : ℤ) ^ (β * r) < (2 : ℤ) ^ (β * r) :=
    Int.emod_lt_of_pos _ (by positivity)
  have hc := resid_cast β r W
  have : ((resid β r W : ℕ) : ℤ) < ((2 : ℕ) ^ (β * r) : ℤ) := by
    rw [hc]; push_cast; exact h
  exact_mod_cast this

theorem pow_split (β i r : ℕ) (hi : i ≤ r) :
    (2 : ℤ) ^ (β * r) = (2 : ℤ) ^ (β * i) * (2 : ℤ) ^ (β * (r - i)) := by
  rw [← pow_add]
  congr 1
  rw [← Nat.mul_add, Nat.add_sub_cancel' hi]

/-- **Chunk identity**: the base-`2^β` digit of `W` at position `i` is the `β`-bit block of the
residue of `W` modulo `2^(β r)` starting at bit `β*i`, provided `i < r`. -/
theorem block_digit (β r : ℕ) (W : ℤ) (i : ℕ) (hi : i < r) :
    ((W / (2 : ℤ) ^ (β * i)) % (2 : ℤ) ^ β).toNat
      = block (resid β r W) (β * i) β := by
  have hile : i ≤ r := by omega
  set Z : ℤ := W / (2 : ℤ) ^ (β * r) with hZ
  have hW : W = (resid β r W : ℤ) + (2 : ℤ) ^ (β * r) * Z := by
    have h := resid_cast β r W
    have h2 := Int.emod_add_mul_ediv W ((2 : ℤ) ^ (β * r))
    rw [hZ, h]; linarith
  have hD : W / (2 : ℤ) ^ (β * i)
      = (resid β r W : ℤ) / (2 : ℤ) ^ (β * i) + (2 : ℤ) ^ (β * (r - i)) * Z := by
    conv_lhs => rw [hW, pow_split β i r hile]
    rw [show (resid β r W : ℤ) + ((2 : ℤ) ^ (β * i) * (2 : ℤ) ^ (β * (r - i))) * Z
          = (resid β r W : ℤ) + (2 : ℤ) ^ (β * i) * ((2 : ℤ) ^ (β * (r - i)) * Z) by ring]
    exact Int.add_mul_ediv_left (resid β r W : ℤ) ((2 : ℤ) ^ (β * (r - i)) * Z)
      (by positivity : ((2 : ℤ) ^ (β * i)) ≠ 0)
  have hbpos : (0 : ℤ) < (2 : ℤ) ^ β := by positivity
  have hsplit2 : (2 : ℤ) ^ (β * (r - i)) = (2 : ℤ) ^ β * (2 : ℤ) ^ (β * (r - i) - β) := by
    rw [← pow_add]
    congr 1
    have h1 : 1 ≤ r - i := by omega
    have h2 : β ≤ β * (r - i) := by
      calc β = β * 1 := by ring
        _ ≤ β * (r - i) := Nat.mul_le_mul_left β h1
    omega
  have hmod : (W / (2 : ℤ) ^ (β * i)) % (2 : ℤ) ^ β
      = ((resid β r W : ℤ) / (2 : ℤ) ^ (β * i)) % (2 : ℤ) ^ β := by
    rw [hD, hsplit2]
    rw [show (2 : ℤ) ^ β * (2 : ℤ) ^ (β * (r - i) - β) * Z
          = (2 : ℤ) ^ β * ((2 : ℤ) ^ (β * (r - i) - β) * Z) by ring]
    rw [Int.add_mul_emod_self_left]
  rw [hmod]
  have hcast : ((resid β r W : ℤ) / (2 : ℤ) ^ (β * i)) % (2 : ℤ) ^ β
      = ((block (resid β r W) (β * i) β : ℕ) : ℤ) := by
    rw [block]
    push_cast
    rfl
  rw [hcast, Int.toNat_natCast]

end UnpackChunk

open UnpackChunk

theorem solution (β r : ℕ) (W : ℤ) (i : ℕ) (hi : i < r) :
    ((W / (2 : ℤ) ^ (β * i)) % (2 : ℤ) ^ β).toNat
      = (W % (2 : ℤ) ^ (β * r)).toNat / 2 ^ (β * i) % 2 ^ β := by
  have := UnpackChunk.block_digit β r W i hi
  simpa [UnpackChunk.block, UnpackChunk.resid] using this
