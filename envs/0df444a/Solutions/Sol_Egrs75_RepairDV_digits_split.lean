-- Prove2me | solution 1 for Egrs75.RepairDV.digits_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:55.665269+00:00
-- url     : https://prove2.me/submissions/3b0dbd17-50b8-4009-9e8d-9c067274d32c

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
theorem _root_.solution {q k Lo Hi : ℕ} (hq : 1 < q) (hLo : Lo < q ^ k) (hHi : 0 < Hi) :
    Nat.digits q (Lo + q ^ k * Hi) =
      Nat.digits q Lo ++ List.replicate (k - (Nat.digits q Lo).length) 0 ++ Nat.digits q Hi := by
  have hlen : (Nat.digits q Lo).length ≤ k := (digits_length_le_iff hq Lo).mpr hLo
  have hpad : (Nat.digits q Lo).length + (k - (Nat.digits q Lo).length) = k := by omega
  rw [digits_append_zeroes_append_digits hq hHi, hpad]
end Egrs75.RepairDV
