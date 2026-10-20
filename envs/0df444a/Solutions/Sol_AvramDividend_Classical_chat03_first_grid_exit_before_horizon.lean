-- Prove2me | solution 1 for AvramDividend.Classical.chat03_first_grid_exit_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:37:25.586526+00:00
-- url     : https://prove2.me/submissions/f42d587e-633c-4075-acf6-6a9bd2268757

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_first_grid_strict_exit_approaches_infimum
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
At every finite continuous strict passage before horizon N, all fine
uniform grids have a genuine first strict exit before N, with no earlier
sampled exit. Does not assume that passage at τ is a strict exit.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (τ N : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hτN : τ < N) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ h : ℝ≥0, 0 < h → h < δ →
      ∃ k : ℕ,
        τ ≤ (k : ℝ≥0) * h ∧
        (k : ℝ≥0) * h < N ∧
        (X.X ((k : ℝ≥0) * h) ω < lower ∨
         upper < X.X ((k : ℝ≥0) * h) ω) ∧
        (∀ j : ℕ, j < k →
          ¬ (X.X ((j : ℝ≥0) * h) ω < lower ∨
             upper < X.X ((j : ℝ≥0) * h) ω)) := by
  obtain ⟨u, hτu, huN⟩ := exists_between hτN
  let ε : ℝ≥0 := u - τ
  have hε : 0 < ε := tsub_pos_iff_lt.mpr hτu
  have hτadd : τ + ε = u := add_tsub_cancel_of_le hτu.le
  obtain ⟨δ, hδ, hmesh⟩ :=
    chat03_first_grid_strict_exit_approaches_infimum
      X ω lower upper τ hτ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhd
  obtain ⟨k, hτk, hkε, hkExit, hkfirst⟩ := hmesh h hh hhd
  have hkN : (k : ℝ≥0) * h < N := by
    calc
      (k : ℝ≥0) * h < τ + ε := hkε
      _ = u := hτadd
      _ < N := huN
  exact ⟨k, hτk, hkN, hkExit, hkfirst⟩