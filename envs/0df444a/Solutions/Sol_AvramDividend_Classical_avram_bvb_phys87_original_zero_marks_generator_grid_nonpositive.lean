-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys87_original_zero_marks_generator_grid_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:23:08.378959+00:00
-- url     : https://prove2.me/submissions/11f4bb56-6f54-43af-9c81-19b1e260df9c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys81_original_zero_marks_weighted_BV_grid_R_sum_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original BV HJB grid inherits its nonpositive sign when the
intrinsic negative marks and the weighted BV remainder vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, i ≤ n + 1 → u n i ≤ T)
    (W : ℕ → ℕ → Ω → ℝ)
    (B G : ℕ → Ω → ℝ)
    (hB : ∀ n ω, B n ω = G n ω +
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         W n i ω * (R (u n i) - R (u n (i + 1)))))
    (hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0) :
    ∀ᵐ ω ∂P,
      (((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω - Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) →
      ∀ n : ℕ, G n ω ≤ 0 := by
  have hR := avram_bvb_phys81_original_zero_marks_weighted_BV_grid_R_sum_zero
    X hX hBV T u hu W
  filter_upwards [hR, hAllB] with ω hRω hAllBω
  intro hZero n
  have hRzero := hRω hZero n
  have hBn : B n ω = G n ω := by
    simpa only [hRzero, add_zero] using hB n ω
  rw [← hBn]
  exact hAllBω n
