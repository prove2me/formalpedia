-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_grid_pair_rate_sum_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T12:40:11.952825+00:00
-- url     : https://prove2.me/submissions/e855a0e7-5f53-4a55-8700-877fb3785ebf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_past_future_count_product_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_marked_rectangle_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (m : ℕ) (s t : Fin m → ℝ≥0)
    (hst : ∀ i, s i ≤ t i)
    (B : Set ℝ) (hB : MeasurableSet B) :
    let N : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞ := fun a b ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc a b ×ˢ B)
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin m, ((s i : ℝ≥0∞) * X.ν B) *
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
  intro N
  have hGrid :
      (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
      ∑ i : Fin m, ∫⁻ ω, N 0 (s i) ω * N (s i) (t i) ω ∂P := by
    apply lintegral_finset_sum
    intro i hi
    apply Measurable.mul
    · exact avram_p2_d_future_intrinsic_marked_rectangle_measurable
        X 0 (s i) B hB
    · exact avram_p2_d_future_intrinsic_marked_rectangle_measurable
        X (s i) (t i) B hB
  calc
    (∫⁻ ω, ∑ i : Fin m, N 0 (s i) ω * N (s i) (t i) ω ∂P) =
        ∑ i : Fin m, ∫⁻ ω, N 0 (s i) ω * N (s i) (t i) ω ∂P :=
      hGrid
    _ = ∑ i : Fin m, ((s i : ℝ≥0∞) * X.ν B) *
          (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν B) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa only [N] using
        (avram_a20_original_borel_past_future_count_product_exact
          X (s i) (t i) (hst i) B hB)
