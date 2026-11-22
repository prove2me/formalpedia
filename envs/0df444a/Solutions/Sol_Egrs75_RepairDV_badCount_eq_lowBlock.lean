-- Prove2me | solution 1 for Egrs75.RepairDV.badCount_eq_lowBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:40:57.071497+00:00
-- url     : https://prove2.me/submissions/09c26dca-91d4-4779-86a6-4e4dc47a7ceb

module
public import Definitions.Def_LeanPool_Egrs75_LeafInduction
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Digits.Lemmas
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Theorems.Thm_Egrs75_RepairDV_badCountQ_split
public import Theorems.Thm_Egrs75_RepairDV_highBlock_lowDigits
public import Theorems.Thm_Egrs75_LeafInduction_badCountQ_eq_zero_iff_lowDigits


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.RepairDV
open Nat
open Egrs75
open Egrs75.LeafInduction
namespace Egrs75.RepairDV
theorem _root_.solution {q n : ℕ} (hq : 1 < q) (hbad : 0 < badCountQ q n) :
    badCountQ q n = badCountQ q (n % q ^ (topBadIndex q n + 1)) := by
  set j := topBadIndex q n with hj
  set k := j + 1 with hk
  have hHi : LowDigits q (n / q ^ k) := highBlock_lowDigits hq hbad
  have hHi0 : badCountQ q (n / q ^ k) = 0 := badCountQ_eq_zero_iff_lowDigits.mpr hHi
  -- n = (n % q^k) + q^k * (n / q^k)
  rcases Nat.eq_zero_or_pos (n / q ^ k) with hHiZero | hHiPos
  · -- high block 0 ⟹ n < q^k, so n % q^k = n
    have : n % q ^ k = n := by
      have hlt : n < q ^ k := by
        rcases Nat.lt_or_ge n (q ^ k) with h | h
        · exact h
        · exact absurd (Nat.div_pos h (by positivity)) (by omega)
      exact Nat.mod_eq_of_lt hlt
    rw [this]
  · have hdecomp : n = n % q ^ k + q ^ k * (n / q ^ k) := by
      rw [Nat.mod_add_div]
    have hLolt : n % q ^ k < q ^ k := Nat.mod_lt _ (by positivity)
    calc badCountQ q n
        = badCountQ q (n % q ^ k + q ^ k * (n / q ^ k)) := by rw [← hdecomp]
      _ = badCountQ q (n % q ^ k) + badCountQ q (n / q ^ k) :=
            badCountQ_split hq hLolt hHiPos
      _ = badCountQ q (n % q ^ k) := by rw [hHi0, add_zero]
end Egrs75.RepairDV
