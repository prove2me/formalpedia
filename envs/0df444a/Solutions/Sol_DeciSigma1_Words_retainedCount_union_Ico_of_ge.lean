-- Prove2me | solution 1 for DeciSigma1.Words.retainedCount_union_Ico_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:45:47.972+00:00
-- url     : https://prove2.me/submissions/3a0ef65d-3b2d-4b15-bbfc-9896b17e79e5

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_not_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_add_of_mem
public import Theorems.Thm_DeciSigma1_Words_retainedCount_union_Ico_of_le

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}
variable {c δ : ℕ}
namespace DeciSigma1.Words
theorem _root_.solution (hD : ∀ p ∈ D, p < c) {p : ℕ} (hp : c + δ ≤ p) :
    retainedCount (D ∪ Finset.Ico c (c + δ)) p = retainedCount D (p - δ) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hin : ∀ i < δ, c + i ∈ D ∪ Finset.Ico c (c + δ) := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  have hout : ∀ i < n, c + δ + i ∉ D ∪ Finset.Ico c (c + δ) := fun i _ h => by
    rcases Finset.mem_union.mp h with h | h
    · have := hD _ h; omega
    · have := (Finset.mem_Ico.mp h).2; omega
  have hout' : ∀ i < n, c + i ∉ D := fun i _ h => by have := hD _ h; omega
  rw [retainedCount_add_of_not_mem hout, retainedCount_add_of_mem hin,
    retainedCount_union_Ico_of_le le_rfl, show c + δ + n - δ = c + n by omega,
    retainedCount_add_of_not_mem hout']
end DeciSigma1.Words
