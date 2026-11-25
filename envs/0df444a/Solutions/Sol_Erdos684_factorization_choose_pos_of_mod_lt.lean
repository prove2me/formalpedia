-- Prove2me | solution 1 for Erdos684.factorization_choose_pos_of_mod_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:19:55.559998+00:00
-- url     : https://prove2.me/submissions/189e7d12-28d0-4572-9996-51429eaf5cbc

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution {n k p : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hmod : n % p < k % p) :
    0 < (n.choose k).factorization p := by
  have hsum := Nat.add_mod k (n - k) p
  rw [Nat.add_sub_of_le hkn] at hsum
  have hkmod := Nat.mod_lt k hp.pos
  have hnmod := Nat.mod_lt (n - k) hp.pos
  have hcarry : p ≤ k % p + (n - k) % p := by
    by_contra h
    have hlt : k % p + (n - k) % p < p := by omega
    rw [Nat.mod_eq_of_lt hlt] at hsum
    omega
  rw [Nat.factorization_choose hp hkn (b := Nat.log p n + 2) (by omega)]
  apply Finset.card_pos.mpr
  refine ⟨1, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_Ico, pow_one]
  exact ⟨⟨by omega, by omega⟩, hcarry⟩
end Erdos684
