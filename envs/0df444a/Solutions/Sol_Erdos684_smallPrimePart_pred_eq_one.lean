-- Prove2me | solution 1 for Erdos684.smallPrimePart_pred_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:04:41.032385+00:00
-- url     : https://prove2.me/submissions/dd66df69-0b50-4662-83a3-18d0acbfa145

module
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Finite
public import Theorems.Thm_Erdos684_factorization_choose_pred_eq_zero

set_option autoImplicit false
@[expose] public section
public section
open Erdos684
namespace Erdos684
theorem _root_.solution {M K : ℕ} (hM : 0 < M)
    (hpowers : ∀ p, p.Prime → p ≤ K → ∃ e, K < p ^ e ∧ p ^ e ∣ M)
    {k : ℕ} (hk : k ≤ K) : smallPrimePart (M - 1) k = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  obtain ⟨hpk, hprime⟩ := Nat.mem_primesLE.mp hp
  obtain ⟨e, hlarge, hdiv⟩ := hpowers p hprime (by omega)
  rw [factorization_choose_pred_eq_zero hM hprime hlarge hdiv hk, pow_zero]
end Erdos684
