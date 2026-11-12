-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja24_original_levy_quadratic_strip_energy_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:56:51.98223+00:00
-- url     : https://prove2.me/submissions/b1fffcf5-ceec-45a9-8498-d3dc6f8cef5d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja23_integral_cutoff_tendsto_of_tail
import Theorems.Thm_AvramDividend_Classical_avram_ja24_finite_negative_quadratic_integrable_on_unit_tail
import Theorems.Thm_AvramDividend_Classical_avram_ja22_original_finite_activity_real_levy_tail_square_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Finite marked-strip quadratic energy exhausts the original negative Levy tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) :
    Tendsto
      (fun m : ℕ => ∫ z in Ioc
        (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1))),
        z ^ 2 ∂X.ν)
      atTop (nhds (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν)) := by
  let q : ℕ → ℝ := fun m => -(1 / ((m : ℝ) + 1))
  have hOrder : ∀ᶠ m in atTop, q n ≤ q m ∧ q m < 0 := by
    filter_upwards [eventually_ge_atTop n] with m hnm
    change (-(1 / ((n : ℝ) + 1))) ≤ (-(1 / ((m : ℝ) + 1))) ∧
      (-(1 / ((m : ℝ) + 1))) < 0
    have hDen : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnm 1
    have hInv : (1 / ((m : ℝ) + 1) : ℝ) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) hDen
    constructor
    · linarith
    · have hp : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have hpInv : (0 : ℝ) < 1 / ((m : ℝ) + 1) := one_div_pos.mpr hp
      linarith
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hFrac : (1 / ((n : ℝ) + 1) : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hA : (-1 : ℝ) ≤ q n := by dsimp [q]; linarith
  have hI := avram_ja24_finite_negative_quadratic_integrable_on_unit_tail
    X.ν (q n) hA hFinite
  have hTail := avram_ja22_original_finite_activity_real_levy_tail_square_tendsto_zero
    X hFinite
  have hLimit := avram_ja23_integral_cutoff_tendsto_of_tail
    X.ν (q n) q hOrder hI hTail
  simpa only [q] using hLimit