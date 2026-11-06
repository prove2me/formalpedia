-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_weighted_intrinsic_jump_drift_grid_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T07:20:56.805943+00:00
-- url     : https://prove2.me/submissions/57a7b760-d7fc-4928-8b20-2d34d5f078f1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Signed finite-grid source bound from the actual original intrinsic jump count,
with nonnegative arbitrary predictable weights and nondecreasing BV residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (s t : Fin n → ℝ≥0)
      (hst : ∀ i, s i ≤ t i) (a : Fin n → ℝ)
      (ha : ∀ i, 0 ≤ a i),
      (∑ i : Fin n, a i *
        (X.X (t i) ω - X.X (s i) ω +
          (∫⁻ p, (if s i < p.1 ∧ p.1 ≤ t i then ENNReal.ofReal (-p.2) else 0) ∂
            ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
              (fun u : ℝ≥0 => (u,
                X.X u ω - Function.leftLim
                  (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ≤
      ∑ i : Fin n, a i * (((t i : ℝ) - (s i : ℝ)) * X.drift) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_source_exact_intrinsic_measure_interval_remainder_decomposition
      X hBV] with ω hω
  obtain ⟨R, _hRdef, hRmono, hRinterval⟩ := hω
  intro n s t hst a ha
  apply Finset.sum_le_sum
  intro i hi
  have hSource := hRinterval (s i) (t i) (hst i)
  have hDown : 0 ≤ R (t i) - R (s i) :=
    sub_nonneg.mpr (hRmono (hst i))
  apply mul_le_mul_of_nonneg_left ?_ (ha i)
  linarith only [hSource, hDown]
