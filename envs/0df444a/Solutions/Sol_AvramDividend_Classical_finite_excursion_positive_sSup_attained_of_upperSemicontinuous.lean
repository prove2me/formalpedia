-- Prove2me | solution 1 for AvramDividend.Classical.finite_excursion_positive_sSup_attained_of_upperSemicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T18:52:42.058283+00:00
-- url     : https://prove2.me/submissions/822217bc-5066-4e8f-9c5d-69947d3f5ecd

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_finite_excursion_height_attained_of_upperSemicontinuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem solution
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (hζ : 0 < ζ)
    (husc : UpperSemicontinuousOn R (Icc 0 ζ))
    (hzero : R 0 = 0) (hEnd : R ζ = 0)
    (hbdd : BddAbove (R '' Icc (0 : ℝ≥0) ζ))
    (hPos : 0 < sSup (R '' Icc (0 : ℝ≥0) ζ)) :
    ∃ T : ℝ≥0, 0 < T ∧ T < ζ ∧
      R T = sSup (R '' Icc (0 : ℝ≥0) ζ) := by
  have hne : (R '' Icc (0 : ℝ≥0) ζ).Nonempty := by
    refine ⟨R 0, 0, ?_, rfl⟩
    exact ⟨le_refl 0, le_of_lt hζ⟩
  have hBound : ∀ t : ℝ≥0, t ≤ ζ →
      R t ≤ sSup (R '' Icc (0 : ℝ≥0) ζ) := by
    intro t ht
    exact le_csSup hbdd ⟨t, ⟨(show (0 : ℝ≥0) ≤ t from zero_le), ht⟩, rfl⟩
  have hSharp : ∀ y : ℝ,
      y < sSup (R '' Icc (0 : ℝ≥0) ζ) →
      ∃ t : ℝ≥0, t ≤ ζ ∧ y < R t := by
    intro y hy
    obtain ⟨b, hb, hyb⟩ := (lt_csSup_iff hbdd hne).mp hy
    rcases hb with ⟨t, ht, rfl⟩
    exact ⟨t, ht.2, hyb⟩
  exact finite_excursion_height_attained_of_upperSemicontinuous
    R ζ hζ husc hzero hEnd
    (sSup (R '' Icc (0 : ℝ≥0) ζ)) hPos hBound hSharp
