-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_sup_bddAbove_of_locally_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:56:44.197148+00:00
-- url     : https://prove2.me/submissions/cf8861af-1305-4f7e-8ff6-90abbecb014e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Order.ConditionallyCompleteLattice.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (D : ℝ → ℝ) (w : ℝ) (hw : 0 ≤ w)
    (hDb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ t : ℝ, t ∈ Ioc (0 : ℝ) R → |D t| ≤ C) :
    ∀ R : ℝ, 0 < R →
      BddAbove ((fun t : ℝ => Real.exp (-(w * t)) * |D t|) ''
        Ioc (0 : ℝ) R) := by
  intro R hR
  obtain ⟨C, hC⟩ := hDb R hR
  refine ⟨C, ?_⟩
  rintro v ⟨t, ht, rfl⟩
  have ht0 : 0 ≤ t := le_of_lt ht.1
  have hnon : 0 ≤ w * t := mul_nonneg hw ht0
  have hexp : Real.exp (-(w * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hnon)
  calc
    Real.exp (-(w * t)) * |D t| ≤ 1 * |D t| :=
      mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    _ = |D t| := one_mul _
    _ ≤ C := hC t ht
