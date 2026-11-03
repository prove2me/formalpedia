-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_bv_finite_activity_weighted_predictable_cell_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:46:43.427695+00:00
-- url     : https://prove2.me/submissions/925e48c3-f7bc-47fd-9025-e5767f20ff29

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Original BV finite-activity marked predictable rectangle compensation
assembled for finite weighted cells, retaining the exact source filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (A : ℕ → Set Ω) (hA : ∀ i ∈ S, MeasurableSet[𝓕 (s i)] (A i))
    (c : ℕ → ℝ≥0∞) :
    (∑ i ∈ S, c i * (∫⁻ ω in A i,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) ∂P)) =
      ∑ i ∈ S, c i * (P (A i) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)))) := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  rw [avram_wave7_01_bv_finite_activity_all_start_actual_negative_predictable_rectangle
    X hBV hFinite (s i) (t i) (hst i hi) (A i) (hA i hi)]
  rw [mul_assoc]
