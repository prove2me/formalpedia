-- Prove2me | solution 1 for Egrs75.RepairDV.lowDigits_disjoint_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:27:12.47988+00:00
-- url     : https://prove2.me/submissions/a891a3b6-3169-446e-a92c-4d410fcafd7a

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution {p k U Hi : ℕ} (hp : 1 < p) (hU : U < p ^ k) (hHi : 0 < Hi)
    (hUlow : LowDigits p U) (hHilow : LowDigits p Hi) : LowDigits p (U + p ^ k * Hi) := by
  unfold LowDigits at *
  have hlen : (Nat.digits p U).length ≤ k := (digits_length_le_iff hp U).mpr hU
  have hpad : (Nat.digits p U).length + (k - (Nat.digits p U).length) = k := by omega
  have hsplit : Nat.digits p (U + p ^ k * Hi) =
      Nat.digits p U ++ List.replicate (k - (Nat.digits p U).length) 0 ++ Nat.digits p Hi := by
    rw [Nat.digits_append_zeroes_append_digits hp hHi, hpad]
  rw [hsplit]
  intro d hd
  rw [List.mem_append, List.mem_append] at hd
  rcases hd with (hd | hd) | hd
  · exact hUlow d hd
  · rw [List.mem_replicate] at hd; rw [hd.2]; exact Nat.zero_le _
  · exact hHilow d hd
end Egrs75.RepairDV
