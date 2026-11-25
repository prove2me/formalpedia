-- Prove2me | solution 1 for ConjCoord.Proof.pell2_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:54:41.137105+00:00
-- url     : https://prove2.me/submissions/12c6abdf-d21b-42c4-b96c-c71912cc9ba1

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
namespace ConjCoord.Proof
theorem _root_.solution {p : ℕ} (h5 : p % 16 = 5) {R S : ℤ}
    (hP : R ^ 2 - 2 * (p : ℤ) * S ^ 2 = 1) : Even S := by
  by_contra hS
  rw [Int.not_even_iff_odd] at hS
  obtain ⟨k, rfl⟩ := hS
  have hp : (p : ℤ) = 8 * ((p / 8 : ℕ) : ℤ) + 5 := by omega
  have := congrArg (Int.cast : ℤ → ZMod 8) hP
  rw [hp] at this
  push_cast at this
  have h8 : (8 : ZMod 8) = 0 := by decide
  rw [h8, zero_mul, zero_add] at this
  generalize (R : ZMod 8) = x at this
  generalize (k : ZMod 8) = y at this
  revert x y this
  decide
end ConjCoord.Proof
