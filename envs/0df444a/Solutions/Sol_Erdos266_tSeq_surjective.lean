-- Prove2me | solution 1 for Erdos266.tSeq_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:38:41.822837+00:00
-- url     : https://prove2.me/submissions/0a21afa1-6559-4f93-82ab-61874c4c668c

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
public import Theorems.Thm_Erdos266_mem_picks
public import Theorems.Thm_Erdos266_pickIdx_injective

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution : Function.Surjective tSeq := by
  intro q
  by_contra hq
  push Not at hq
  set m := qEnum.symm q with hm
  -- at every late enough stage, `q` is a candidate, so the greedy index is `≤ m`
  have key : ∀ i : ℕ, |q| ≤ (i : ℚ) + 1 → pickIdx i ≤ m := by
    intro i hqi
    apply Nat.find_min'
    constructor
    · rw [hm, Equiv.apply_symm_apply, mem_picks]
      rintro ⟨j, _, hjq⟩
      exact hq j hjq
    · rw [hm, Equiv.apply_symm_apply]
      exact hqi
  have hbound : ∀ i, ⌈|q|⌉₊ ≤ i → pickIdx i ≤ m := by
    intro i hi
    apply key
    calc |q| ≤ (⌈|q|⌉₊ : ℚ) := Nat.le_ceil _
    _ ≤ (i : ℚ) := by exact_mod_cast hi
    _ ≤ (i : ℚ) + 1 := by linarith
  -- pigeonhole: `m + 2` stages, at most `m + 1` available indices
  have hmaps : ∀ i ∈ Finset.Icc ⌈|q|⌉₊ (⌈|q|⌉₊ + m + 1),
      pickIdx i ∈ Finset.range (m + 1) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact hbound i (Finset.mem_Icc.mp hi).1
  have hinj : Set.InjOn pickIdx (Finset.Icc ⌈|q|⌉₊ (⌈|q|⌉₊ + m + 1)) :=
    fun a _ b _ h => pickIdx_injective h
  have hcard := Finset.card_le_card_of_injOn pickIdx hmaps hinj
  rw [Nat.card_Icc, Finset.card_range] at hcard
  omega
end Erdos266
