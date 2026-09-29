-- Prove2me | solution 1 for FiniteLattice.weighted_weisner_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-22T14:42:27.459038+00:00
-- url     : https://prove2.me/submissions/a7359247-9de6-4400-ab48-0d578b4af9be

import Mathlib

set_option autoImplicit false

namespace MagicSquaresSpencer

open Finset
attribute [local instance] Classical.propDecidable

/-- Weighted finite Weisner cancellation. Only the interval sums above `a` are needed. -/
theorem weighted_weisner {L : Type*} [Lattice L] [Fintype L] [DecidableEq L]
    (d a b : L) (w : L → ℚ) (hab : a ≤ b)
    (hzero : ∀ x : L, a ≤ x → x ≤ b →
      (∑ c ∈ (Finset.univ : Finset L).filter (fun c => d ≤ c ∧ c ≤ x), w c) = 0) :
    (∑ c ∈ (Finset.univ : Finset L).filter
      (fun c => d ≤ c ∧ c ≤ b ∧ c ⊔ a = b), w c) = 0 := by
  classical
  let fibre (y : L) : ℚ :=
    ∑ c ∈ (Finset.univ : Finset L).filter
      (fun c => d ≤ c ∧ c ≤ b ∧ c ⊔ a = y), w c
  have hfibre (y : L) : fibre y =
      ∑ c ∈ (Finset.univ : Finset L).filter
        (fun c => d ≤ c ∧ c ≤ b),
        if c ⊔ a = y then w c else 0 := by
    simp only [fibre, ← Finset.filter_filter]
    exact Finset.sum_filter _ _
  have hprefix (x : L) (hax : a ≤ x) (hxb : x ≤ b) :
      (∑ y ∈ (Finset.univ : Finset L).filter
        (fun y => a ≤ y ∧ y ≤ x), fibre y) = 0 := by
    have hsum :
        (∑ y ∈ (Finset.univ : Finset L).filter
          (fun y => a ≤ y ∧ y ≤ x), fibre y) =
          ∑ c ∈ (Finset.univ : Finset L).filter
            (fun c => d ≤ c ∧ c ≤ x), w c := by
      simp_rw [hfibre]
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ,
        true_and, le_sup_right, true_and]
      simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      have hset :
          ((Finset.univ : Finset L).filter (fun c => d ≤ c ∧ c ≤ b)).filter
            (fun c => c ⊔ a ≤ x) =
          (Finset.univ : Finset L).filter (fun c => d ≤ c ∧ c ≤ x) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hdc, -⟩, hc⟩
          exact ⟨hdc, (le_sup_left).trans hc⟩
        · rintro ⟨hdc, hcx⟩
          exact ⟨⟨hdc, hcx.trans hxb⟩, sup_le hcx hax⟩
      rw [hset]
    exact hsum.trans (hzero x hax hxb)
  have hall : ∀ x : L, a ≤ x → x ≤ b → fibre x = 0 := by
    intro x
    induction x using (wellFounded_lt (α := L)).induction with
    | h x ih =>
      intro hax hxb
      have hs := hprefix x hax hxb
      have hsingle :
          (∑ y ∈ (Finset.univ : Finset L).filter
            (fun y => a ≤ y ∧ y ≤ x), fibre y) = fibre x := by
        apply Finset.sum_eq_single_of_mem x
        · simp [hax]
        · intro y hy hyx
          have hy' : a ≤ y ∧ y ≤ x := by simpa using hy
          have hlt : y < x := lt_of_le_of_ne hy'.2 hyx
          exact ih y hlt hy'.1 (hy'.2.trans hxb)
      exact hsingle.symm.trans hs
  exact hall b hab le_rfl

end MagicSquaresSpencer

attribute [local instance] Classical.propDecidable

/-- Platform-facing instance of the proved weighted finite Weisner cancellation. -/
theorem solution {L : Type*} [Lattice L] [Fintype L] [DecidableEq L]
    (d a b : L) (w : L → ℚ) (hab : a ≤ b)
    (hzero : ∀ x : L, a ≤ x → x ≤ b →
      (∑ c ∈ (Finset.univ : Finset L).filter (fun c => d ≤ c ∧ c ≤ x), w c) = 0) :
    (∑ c ∈ (Finset.univ : Finset L).filter
      (fun c => d ≤ c ∧ c ≤ b ∧ c ⊔ a = b), w c) = 0 :=
  MagicSquaresSpencer.weighted_weisner d a b w hab hzero
