-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_sup_contraction_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:07:26.526991+00:00
-- url     : https://prove2.me/submissions/cffb7305-f507-4256-97c3-6652c85c4605

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A strict finite-horizon weighted-supremum contraction is zero. -/
theorem solution
    (D : ℝ → ℝ) (w c : ℝ) (hc : c < 1)
    (hbound : ∀ R : ℝ, 0 < R →
      BddAbove ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) '' Ioc (0 : ℝ) R))
    (hcontraction : ∀ R : ℝ, 0 < R → ∀ t ∈ Ioc (0 : ℝ) R,
      Real.exp (-(w * t)) * |D t| ≤
        c * sSup ((fun u : ℝ => Real.exp (-(w * u)) * |D u|) ''
          Ioc (0 : ℝ) R)) :
    ∀ t : ℝ, 0 < t → D t = 0 := by
  intro t ht
  let f : ℝ → ℝ := fun u => Real.exp (-(w * u)) * |D u|
  let S : Set ℝ := f '' Ioc (0 : ℝ) t
  have htmem : t ∈ Ioc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hSnonempty : S.Nonempty := ⟨f t, ⟨t, htmem, rfl⟩⟩
  have hSbdd : BddAbove S := hbound t ht
  have hSnonneg : 0 ≤ sSup S := by
    calc
      0 ≤ f t := mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
      _ ≤ sSup S := le_csSup hSbdd ⟨t, htmem, rfl⟩
  have hScontr : sSup S ≤ c * sSup S := by
    apply csSup_le hSnonempty
    rintro y ⟨u, hu, rfl⟩
    exact hcontraction t ht u hu
  have hSupZero : sSup S ≤ 0 := by
    by_contra h
    have hp : 0 < sSup S := lt_of_not_ge h
    have hprod : 0 < (1 - c) * sSup S := mul_pos (by linarith) hp
    nlinarith
  have hfZero : f t = 0 := by
    apply le_antisymm
    · exact (le_csSup hSbdd ⟨t, htmem, rfl⟩).trans hSupZero
    · exact mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  have hAbsZero : |D t| = 0 := by
    have : Real.exp (-(w * t)) * |D t| = 0 := hfZero
    rcases mul_eq_zero.mp this with he | he
    · exact False.elim ((Real.exp_ne_zero _ ) he)
    · exact he
  exact abs_eq_zero.mp hAbsZero
