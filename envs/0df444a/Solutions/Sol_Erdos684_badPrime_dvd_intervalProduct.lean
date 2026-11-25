-- Prove2me | solution 1 for Erdos684.badPrime_dvd_intervalProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:55:59.544637+00:00
-- url     : https://prove2.me/submissions/0beafcce-1c94-4df9-af7d-3bb1aea6c329

module
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_BadPrimes
public import Theorems.Thm_Erdos684_dvd_add_residue_gap

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution {n X A p : ℕ}
    (hp : p ∈ badPrimes n X A) :
    p ∣ ∏ j ∈ Finset.Icc 1 A, (n + j) := by
  obtain ⟨hpX, hgap⟩ := Finset.mem_filter.mp hp
  have hprime := Nat.prime_of_mem_primesLE hpX
  have hpos : 1 ≤ p - n % p := by
    have hr := Nat.mod_lt n hprime.pos
    omega
  exact (dvd_add_residue_gap n p hprime.pos).trans
    (Finset.dvd_prod_of_mem (fun j => n + j) (Finset.mem_Icc.mpr ⟨hpos, hgap⟩))
end Erdos684
