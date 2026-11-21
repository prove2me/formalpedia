-- Prove2me | solution 1 for Champernowne.sum_Ico_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:33.967175+00:00
-- url     : https://prove2.me/submissions/8ada6836-a7f2-4706-bf12-5e061147b219

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {β : Type*} [AddCommMonoid β] {b : ℕ} (hb : 1 < b)
    (M : ℕ) (g : ℕ → β) :
    ∑ n ∈ Finset.Ico 1 (b ^ M), g n
      = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Ico (b ^ (m - 1)) (b ^ m), g n := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [← Finset.sum_Ico_consecutive g
        (Nat.one_le_pow M b (by omega))
        (Nat.pow_le_pow_right (by omega) (Nat.le_add_right M 1)),
      ih, Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
end Champernowne
