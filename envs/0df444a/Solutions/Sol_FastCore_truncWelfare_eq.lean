-- Prove2me | solution 1 for FastCore.truncWelfare_eq
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:46:33.055629+00:00
-- url     : https://prove2.me/submissions/6ce29284-ecb0-4756-b289-2308d37c3f8f

import Mathlib
import Definitions.Def_FastCore_IsBidProfile
import Definitions.Def_FastCore_w
import Definitions.Def_FastCore_trunc
import Definitions.Def_FastCore_IsZeroFreeWinnerSet

set_option autoImplicit false

open FastCore ComplementFreeCA.CFRounding

namespace FastCore.TruncProof

theorem le_w {n m : ℕ} {b : Bids n m} {S : Finset (Fin n)} {x : Fin n → Finset (Fin m)}
    (hx : IsAllocation x) (hS : ∀ i, i ∉ S → x i = ∅) : welfare b x ≤ w b S := by
  classical
  unfold w
  exact Finset.le_sup' (welfare b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hS⟩)

theorem w_le {n m : ℕ} {b : Bids n m} {S : Finset (Fin n)} {c : ℝ}
    (h : ∀ x, IsAllocation x → (∀ i, i ∉ S → x i = ∅) → welfare b x ≤ c) : w b S ≤ c := by
  classical
  unfold w
  apply Finset.sup'_le
  intro x hx
  rw [Finset.mem_filter] at hx
  exact h x hx.2.1 hx.2.2

theorem sum_pi_eq {n : ℕ} (S : Finset (Fin n)) (π : Fin n → ℝ) :
    ∑ i ∈ S, π i = ∑ i, (if i ∈ S then π i else 0) := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

end FastCore.TruncProof

open FastCore.TruncProof in
theorem solution {n m : ℕ} {b : Bids n m} (hb : IsBidProfile b) {π : Fin n → ℝ}
    (hπ : ∀ i, 0 ≤ π i) :
    (∀ S, IsZeroFreeWinnerSet (trunc b π) S →
        w (trunc b π) Finset.univ = w b S - ∑ i ∈ S, π i) ∧
      ∀ S, w b S - ∑ i ∈ S, π i ≤ w (trunc b π) Finset.univ := by
  have partB : ∀ S, w b S - ∑ i ∈ S, π i ≤ w (trunc b π) Finset.univ := by
    intro S
    have : w b S ≤ w (trunc b π) Finset.univ + ∑ i ∈ S, π i := by
      apply w_le
      intro x hx hS
      have h1 : welfare b x - ∑ i ∈ S, π i ≤ welfare (trunc b π) x := by
        rw [sum_pi_eq, welfare, welfare, ← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum
        intro i _
        simp only [trunc]
        by_cases hi : i ∈ S
        · rw [if_pos hi]
          exact le_max_left _ _
        · rw [if_neg hi, hS i hi, hb.1 i, sub_zero]
          exact le_max_right _ _
      have h2 : welfare (trunc b π) x ≤ w (trunc b π) Finset.univ :=
        le_w hx (fun i hi => absurd (Finset.mem_univ i) hi)
      linarith
    linarith
  refine ⟨?_, partB⟩
  rintro S ⟨x, ⟨hxa, hxmax⟩, hpos, rfl⟩
  have hw : w (trunc b π) Finset.univ = welfare (trunc b π) x :=
    le_antisymm (w_le (fun y hy _ => hxmax y hy))
      (le_w hxa (fun i hi => absurd (Finset.mem_univ i) hi))
  have hsupp : ∀ i, i ∉ winners x → x i = ∅ := by
    intro i hi
    simp only [winners, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    exact hi
  have hval : welfare (trunc b π) x = welfare b x - ∑ i ∈ winners x, π i := by
    rw [sum_pi_eq, welfare, welfare, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [trunc]
    by_cases hi : x i = ∅
    · have hni : i ∉ winners x := by simp [winners, hi]
      rw [if_neg hni, hi, hb.1 i, max_eq_right (by linarith [hπ i])]
      ring
    · have hwi : i ∈ winners x := by simp [winners, hi]
      rw [if_pos hwi]
      have := hpos i hi
      simp only [trunc] at this
      apply max_eq_left
      by_contra hc
      push Not at hc
      rw [max_eq_right hc.le] at this
      exact lt_irrefl _ this
  have hle : welfare b x ≤ w b (winners x) := le_w hxa hsupp
  apply le_antisymm
  · rw [hw, hval]
    linarith
  · exact partB _
