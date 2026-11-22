-- Prove2me | solution 1 for CriticalPortraits.discrete_ivt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:15.658171+00:00
-- url     : https://prove2.me/submissions/6eaeef55-cce7-4756-884c-61c1495cc677

module
public import Definitions.Def_LeanPool_CriticalPortraits_Injectivity
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Positivity.Finset
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CriticalPortraits_Surjectivity

set_option autoImplicit true
@[expose] public section
public section
open CriticalPortraits
open Finset
open scoped BigOperators
namespace CriticalPortraits
theorem _root_.solution (D : ℕ → ℤ) (L : ℕ) (h0 : D 0 ≤ 0) (hL : 0 ≤ D L)
    (hstep : ∀ k, k < L → D (k + 1) ≤ D k + 1) : ∃ k ≤ L, D k = 0 := by
  classical
  set K := Nat.findGreatest (fun k => D k ≤ 0) L with hK
  have hspec : D K ≤ 0 := by
    have := Nat.findGreatest_spec (P := fun k => D k ≤ 0) (m := 0) (Nat.zero_le L) h0
    simp only [hK]; exact this
  have hKle : K ≤ L := Nat.findGreatest_le L
  refine ⟨K, hKle, ?_⟩
  rcases Nat.lt_or_ge K L with hlt | hge
  · -- K < L: findGreatest is greatest, so ¬(D (K+1) ≤ 0), i.e. 0 < D (K+1)
    have hnot : ¬ (D (K+1) ≤ 0) := by
      have := Nat.findGreatest_is_greatest (P := fun k => D k ≤ 0)
        (k := K+1) (n := L) (by simp [hK]) hlt
      simpa using this
    have hpos : 0 < D (K+1) := by omega
    have := hstep K hlt
    omega
  · -- K ≥ L, with K ≤ L, so K = L; use hL
    have hKeq : K = L := le_antisymm hKle hge
    rw [hKeq] at hspec ⊢
    omega
end CriticalPortraits
