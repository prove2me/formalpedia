-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_source_locally_finite_jump_times_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:51:02.880754+00:00
-- url     : https://prove2.me/submissions/8ea25132-3896-4b68-97bb-75de3e2606a8

import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- One original P-full event supports finite genuine X jumps on every
bounded nonnegative horizon, without replacing or altering the source path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      {t : ℝ≥0 |
        t ≤ T ∧ 0 < t ∧
          X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0}.Finite := by
  have hInteger : ∀ᵐ ω ∂P, ∀ n : ℕ,
      {t : ℝ≥0 |
        t ≤ ((n + 1 : ℕ) : ℝ≥0) ∧ 0 < t ∧
          X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0}.Finite := by
    rw [ae_all_iff]
    intro n
    exact avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
      X hBV hFinite ((n + 1 : ℕ) : ℝ≥0) (by positivity)
  filter_upwards [hInteger] with ω hω
  intro T
  obtain ⟨n, hn⟩ := exists_nat_gt T
  have hTn : T ≤ ((n + 1 : ℕ) : ℝ≥0) := by
    exact le_trans (le_of_lt hn) (by exact_mod_cast Nat.le_succ n)
  apply (hω n).subset
  rintro t ⟨ht, hpos, hmark⟩
  exact ⟨le_trans ht hTn, hpos, hmark⟩
