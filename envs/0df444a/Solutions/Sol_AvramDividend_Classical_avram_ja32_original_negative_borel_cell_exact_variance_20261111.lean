-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja32_original_negative_borel_cell_exact_variance_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:41:43.126203+00:00
-- url     : https://prove2.me/submissions/3d2522b3-5fdd-48b1-9e3e-a4ca5932e4c2

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja36_original_negative_borel_cell_factorial_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja19_square_integrable_of_ae_sum_components
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_compensated_variance_of_factorial_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact physical negative Borel cell variance from its true-source factorial pair moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    let Y : Ω → ℝ := fun ω => (N ω).toReal - r
    Integrable (fun ω => (Y ω) ^ 2) P ∧
      (∫ ω, (Y ω) ^ 2 ∂P) = r := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)
  let J : Ω → ℝ := fun ω => (N ω).toReal
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = r
  haveI : IsProbabilityMeasure P := X.isProbability
  have hFirst : Integrable J P ∧ (∫ ω, J ω ∂P) = r := by
    simpa [N, J, r] using
      (avram_ja35_original_negative_borel_real_count_first_moment
        X hFinite T B hB hNeg)
  have hFact : Integrable (fun ω => J ω * (J ω - 1)) P ∧
      (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2 := by
    simpa [N, J, r] using
      (avram_ja36_original_negative_borel_cell_factorial_moment
        X hFinite T B hB hNeg)
  have hJ2 : Integrable (fun ω => (J ω) ^ 2) P := by
    have hEq : (fun ω : Ω => (J ω) ^ 2) =
        (fun ω => J ω * (J ω - 1) + J ω) := by
      funext ω
      ring
    rw [hEq]
    exact hFact.1.add hFirst.1
  have hC : Integrable (fun ω => (J ω - r) ^ 2) P := by
    apply avram_ja19_square_integrable_of_ae_sum_components
      (fun ω => J ω - r) J (fun _ => -r)
      (hFirst.1.aestronglyMeasurable.sub aestronglyMeasurable_const)
      hJ2 (integrable_const _)
    filter_upwards [] with ω
    ring
  have hSource (ω : Ω) : J ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal := rfl
  have hRate : r =
      ((((T - 0 : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal := by
    simp [r]
  have hVar :=
    avram_p4_b_smalljump_original_finite_band_compensated_variance_of_factorial_moment
      X 0 T B J hSource hFirst.1 hFact.1 r hRate hFirst.2 hFact.2
  exact ⟨hC, hVar⟩
