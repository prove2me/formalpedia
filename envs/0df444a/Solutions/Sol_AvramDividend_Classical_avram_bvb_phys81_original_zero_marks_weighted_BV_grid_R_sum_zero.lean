-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_phys81_original_zero_marks_weighted_BV_grid_R_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:39:21.30507+00:00
-- url     : https://prove2.me/submissions/216917db-2397-43cb-812d-f9077cc54167

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys80_original_zero_marks_BV_drift_remainder_vanishes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The signed BV remainder contribution to every physical stopped grid is
zero on the original negative-mark-free event, for arbitrary cell weights. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, i ≤ n + 1 → u n i ≤ T)
    (W : ℕ → ℕ → Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧
        X.X v ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v, X.X v ω - Function.leftLim
          (fun z : ℝ≥0 => X.X z ω) v)))
        (Ioc 0 T ×ˢ Iio (0 : ℝ)) = 0) →
      ∀ n : ℕ,
        (let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           W n i ω * (R (u n i) - R (u n (i + 1)))) = 0 := by
  filter_upwards [avram_bvb_phys80_original_zero_marks_BV_drift_remainder_vanishes
    X hX hBV T] with ω hR
  intro hZero n
  dsimp only
  apply Finset.sum_eq_zero
  intro i hi
  have hi_lt : i < n + 1 := Finset.mem_range.mp hi
  have hi_bound : u n i ≤ T := hu n i (by omega)
  have hin_bound : u n (i + 1) ≤ T := hu n (i + 1) (by omega)
  rw [hR hZero (u n i) hi_bound, hR hZero (u n (i + 1)) hin_bound]
  ring
