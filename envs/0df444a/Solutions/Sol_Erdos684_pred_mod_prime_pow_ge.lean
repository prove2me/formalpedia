-- Prove2me | solution 1 for Erdos684.pred_mod_prime_pow_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:48:52.662701+00:00
-- url     : https://prove2.me/submissions/ad6ce3da-a0d6-489c-82cb-06087ec9f225

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite
public import Theorems.Thm_Erdos684_pred_mod_of_dvd

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution {M K p e : ℕ} (hM : 0 < M) (hp : p.Prime)
    (hlarge : K < p ^ e) (hdiv : p ^ e ∣ M) {k : ℕ} (hk : k ≤ K) (i : ℕ) :
    k % p ^ i ≤ (M - 1) % p ^ i := by
  have hpow : 0 < p ^ i := pow_pos hp.pos _
  by_cases hi : i ≤ e
  · have hd : p ^ i ∣ M := (Nat.pow_dvd_pow p hi).trans hdiv
    rw [pred_mod_of_dvd hM hpow hd]
    have hmod := Nat.mod_lt k hpow
    omega
  · have hd : p ^ e ∣ p ^ i := Nat.pow_dvd_pow p (by omega)
    have hmod := Nat.mod_mod_of_dvd (M - 1) hd
    have hle := Nat.mod_le ((M - 1) % p ^ i) (p ^ e)
    rw [hmod, pred_mod_of_dvd hM (pow_pos hp.pos _) hdiv] at hle
    have hkmod := Nat.mod_le k (p ^ i)
    omega
end Erdos684
