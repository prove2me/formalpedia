-- Prove2me | solution 1 for Egrs75.ClearingP2.add_U_lowDigits_p
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:40.360457+00:00
-- url     : https://prove2.me/submissions/ea6d505c-bb83-4c69-bf94-c247cd5010a9

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Definitions.Def_LeanPool_Egrs75_DigitAtToolkit
public import Definitions.Def_LeanPool_Egrs75_DigitVector
public import Definitions.Def_LeanPool_Egrs75_RoundUp
public import Definitions.Def_LeanPool_Egrs75_AddBranch
public import Theorems.Thm_Egrs75_ClearingP2_lowDigits_div_pow
public import Theorems.Thm_Egrs75_RepairDV_lowDigits_disjoint_add


set_option autoImplicit true
@[expose] public section
public section
open Egrs75 Egrs75.ClearingP2
open Nat
open Egrs75
open Egrs75.LeafInduction
open Egrs75.RepairDV
open Egrs75.RepairPaperfaithful
namespace Egrs75.ClearingP2
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p) {n m U : ℕ}
    (hpn : LowDigits p n) (hpU : LowDigits p U) (hUlt : U < p ^ m)
    (hm : n % p ^ m = 0) (hnpos : 0 < n) : LowDigits p (n + U) := by
  have hp1 : 1 < p := by omega
  -- p^m ∣ n  ⟹  n = p^m * (n / p^m)
  have hdvd : p ^ m ∣ n := Nat.dvd_of_mod_eq_zero hm
  obtain ⟨H, hH⟩ := hdvd            -- n = p^m * H
  -- High block H = n / p^m is positive (n > 0).
  have hHpos : 0 < H := by
    simp_all
  have hHlow : LowDigits p H := by
    have : H = n / p ^ m := by
      rw [hH, Nat.mul_div_cancel_left _ (pow_pos (by omega) m)]
    rw [this]; exact lowDigits_div_pow hp hpn
  -- n + U = U + p^m * H, a disjoint-support base-`p` sum.
  have hrw : n + U = U + p ^ m * H := by rw [hH]; ring
  rw [hrw]
  exact lowDigits_disjoint_add hp1 hUlt hHpos hpU hHlow
end Egrs75.ClearingP2
