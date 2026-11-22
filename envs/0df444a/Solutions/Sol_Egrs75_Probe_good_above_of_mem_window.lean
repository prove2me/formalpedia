-- Prove2me | solution 1 for Egrs75.Probe.good_above_of_mem_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:31.534041+00:00
-- url     : https://prove2.me/submissions/4b229dce-ed2b-4e30-8868-ec59066fad34

module
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_ClearingHigh

set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.Probe
open Nat
open Egrs75
open Egrs75.RepairPaperfaithful
namespace Egrs75.Probe
theorem _root_.solution {q j m : ℕ} (hq : 3 ≤ q)
    (hlo : q ^ j ≤ m) (hhi : m < 2 * q ^ j) :
    ∀ i, j ≤ i → m / q ^ i % q ≤ (q - 1) / 2 := by
  intro i hi
  have hqpos : 0 < q ^ j := pow_pos (by omega) j
  rcases eq_or_lt_of_le hi with rfl | hlt
  · -- i = j: m / q^j = 1, so digit = 1 % q = 1 ≤ (q-1)/2
    have h1 : m / q ^ j = 1 := by
      have hub : m < (1 + 1) * q ^ j := by rw [add_mul, one_mul]; omega
      have hlb : 1 * q ^ j ≤ m := by rw [one_mul]; exact hlo
      exact Nat.div_eq_of_lt_le hlb hub
    rw [h1, Nat.mod_eq_of_lt (show (1:ℕ) < q by omega)]
    omega
  · -- i > j: m / q^i = 0 since m < 2*q^j ≤ q^(j+1) ≤ q^i
    have hstep : 2 * q ^ j ≤ q ^ (j + 1) := by
      rw [pow_succ]; nlinarith [pow_pos (show 0 < q by omega) j]
    have hle : q ^ (j + 1) ≤ q ^ i := Nat.pow_le_pow_right (by omega) hlt
    have : m < q ^ i := by omega
    rw [Nat.div_eq_of_lt this]
    simp
end Egrs75.Probe
