-- Prove2me | solution 1 for BulteauTranspositions.NPHard.property_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:46:22.382138+00:00
-- url     : https://prove2.me/submissions/b1f26d65-af97-4b96-a3dd-0f62950f97e1

import Mathlib
import Definitions.Def_BulteauTranspositions_NPHard_Sorting

namespace Aux_BTp4

open BulteauTranspositions.NPHard

def bset (n : ℕ) (p : ℕ → ℕ) : Finset ℕ := (Finset.Icc 1 n).filter fun x => p x ≠ p (x - 1) + 1

theorem one_move (n : ℕ) (p : ℕ → ℕ) (c : Cut) (hc : c.Legal n) :
    breakpoints n p ≤ breakpoints n (applyMove p c) + 3 := by
  obtain ⟨hi, hij, hjk, hkn⟩ := hc
  have hsub : bset n p ⊆ (bset n (applyMove p c)).image c.tau ∪ {c.i, c.j, c.k} := by
    intro y hy
    unfold bset at hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    obtain ⟨⟨hy1, hyn⟩, hyb⟩ := hy
    by_cases hS : y = c.i ∨ y = c.j ∨ y = c.k
    · apply Finset.mem_union_right
      rcases hS with h | h | h <;> simp [h]
    · apply Finset.mem_union_left
      push_neg at hS
      obtain ⟨hs1, hs2, hs3⟩ := hS
      let x := if y < c.i then y else if y < c.j then y + c.k - c.j
        else if y < c.k then y - c.j + c.i else y
      have hx1 : 1 ≤ x ∧ x ≤ n := by
        simp only [x]; split_ifs <;> omega
      have htx : c.tau x = y := by
        simp only [x, Cut.tau]; split_ifs <;> omega
      have htx1 : c.tau (x - 1) = y - 1 := by
        simp only [x, Cut.tau]; split_ifs <;> omega
      rw [Finset.mem_image]
      refine ⟨x, ?_, htx⟩
      unfold bset
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨hx1, ?_⟩
      unfold applyMove
      simp only [Function.comp]
      rw [htx, htx1]
      exact hyb
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((bset n (applyMove p c)).image c.tau) {c.i, c.j, c.k}
  have h3 := Finset.card_image_le (s := bset n (applyMove p c)) (f := c.tau)
  have h4 : ({c.i, c.j, c.k} : Finset ℕ).card ≤ 3 := Finset.card_le_three
  unfold breakpoints
  change (bset n p).card ≤ (bset n (applyMove p c)).card + 3
  omega

theorem many (n : ℕ) (cs : List Cut) : ∀ p : ℕ → ℕ, (∀ c ∈ cs, c.Legal n) →
    breakpoints n p ≤ breakpoints n (movesResult p cs) + 3 * cs.length := by
  induction cs with
  | nil => intro p _; simp [movesResult]
  | cons c cs ih =>
    intro p hcs
    have h1 := one_move n p c (hcs c (List.mem_cons_self))
    have h2 := ih (applyMove p c) (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
    have : movesResult p (c :: cs) = movesResult (applyMove p c) cs := rfl
    rw [this, List.length_cons]
    omega

theorem sorted_zero (n : ℕ) (r : ℕ → ℕ) (hr : ∀ x ≤ n, r x = x) : breakpoints n r = 0 := by
  unfold breakpoints
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  rw [Finset.mem_Icc] at hx
  rw [hr x hx.2, hr (x - 1) (by omega)]
  omega

end Aux_BTp4

open BulteauTranspositions.NPHard Aux_BTp4 in
theorem solution (n : ℕ) (p : ℕ → ℕ) (hp : IsPermutation n p) :
    (breakpoints n p : ℕ∞) ≤ 3 * distance n p := by
  have hall : ∀ cs : List Cut, SortingSequence n p cs → breakpoints n p ≤ 3 * cs.length := by
    intro cs ⟨hleg, hsort⟩
    have := many n cs p hleg
    rw [sorted_zero n _ hsort] at this
    omega
  unfold distance
  set S := {k : ℕ∞ | ∃ cs : List Cut, SortingSequence n p cs ∧ k = (cs.length : ℕ∞)} with hS
  rcases Set.eq_empty_or_nonempty S with h | h
  · rw [h, sInf_empty]
    simp
  · obtain ⟨cs, hcs, hk⟩ := csInf_mem h
    rw [hk]
    have := hall cs hcs
    exact_mod_cast this
