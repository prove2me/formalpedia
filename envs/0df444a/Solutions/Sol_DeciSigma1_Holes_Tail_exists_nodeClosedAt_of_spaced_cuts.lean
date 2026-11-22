-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.exists_nodeClosedAt_of_spaced_cuts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:50:56.51278+00:00
-- url     : https://prove2.me/submissions/246373b5-f076-42c6-a911-90172d85a322

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_dictSuffix_mem
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_PeriodicFrom_add_mul


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] {D : Finset (List α)}
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [Fintype S] (T : Table α S k) (q0 : S) (hD : [] ∈ D)
    (x : List α) {s u : ℕ} (hs : 0 < s) (hu : u + s * (D.card * Fintype.card S) ≤ x.length) :
    ∃ c c', u ≤ c ∧ c' ≤ u + s * (D.card * Fintype.card S) ∧ s ≤ c' - c ∧
      NodeClosedAt T q0 D x c c' := by
  set V := D.card * Fintype.card S
  have hmaps : ∀ j ∈ Finset.range (V + 1),
      suffixNode T q0 D (x.take (u + j * s)) ∈ D ×ˢ (Finset.univ : Finset S) := fun j _ =>
    Finset.mem_product.mpr ⟨dictSuffix_mem hD _, Finset.mem_univ _⟩
  have hcard : (D ×ˢ (Finset.univ : Finset S)).card < (Finset.range (V + 1)).card := by
    rw [Finset.card_product, Finset.card_univ, Finset.card_range]; omega
  obtain ⟨j₁, hj₁, j₂, hj₂, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at hj₁ hj₂
  have key : ∀ i j, i < j → j < V + 1 →
      suffixNode T q0 D (x.take (u + i * s)) = suffixNode T q0 D (x.take (u + j * s)) →
      ∃ c c', u ≤ c ∧ c' ≤ u + s * V ∧ s ≤ c' - c ∧ NodeClosedAt T q0 D x c c' := by
    intro i j hij hj heq
    have h1 : (i + 1) * s ≤ j * s := Nat.mul_le_mul_right s hij
    have h2 : j * s ≤ V * s := Nat.mul_le_mul_right s (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    rw [Nat.mul_comm s V] at hu ⊢
    exact ⟨u + i * s, u + j * s, by omega, by omega, by omega, by omega, by omega, heq⟩
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key j₁ j₂ h hj₂ he
  · exact key j₂ j₁ h hj₁ he.symm
end DeciSigma1.Holes.Tail
