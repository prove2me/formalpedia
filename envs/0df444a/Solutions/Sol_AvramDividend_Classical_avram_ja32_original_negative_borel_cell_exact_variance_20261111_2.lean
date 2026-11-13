-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja32_original_negative_borel_cell_exact_variance_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T09:02:39.908704+00:00
-- url     : https://prove2.me/submissions/51149c22-e966-4035-bd66-feac564b2054

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja36_original_negative_borel_cell_factorial_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    let Y : Ω → ℝ := fun ω =>
      (NX ω (Ioc 0 T ×ˢ B)).toReal - r
    Integrable (fun ω => (Y ω) ^ 2) P ∧
      (∫ ω, (Y ω) ^ 2 ∂P) = r := by
  letI : IsProbabilityMeasure P := X.isProbability
  let J : Ω → ℝ := fun ω =>
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B)).toReal
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => (J ω - r) ^ 2) P ∧
    (∫ ω, (J ω - r) ^ 2 ∂P) = r
  obtain ⟨hJI, hJ⟩ : Integrable J P ∧ (∫ ω, J ω ∂P) = r := by
    simpa only [J, r] using
      (avram_ja35_original_negative_borel_real_count_first_moment
        X hFinite T B hB hNeg)
  obtain ⟨hFI, hF⟩ : Integrable (fun ω => J ω * (J ω - 1)) P ∧
      (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2 := by
    simpa only [J, r] using
      (avram_ja36_original_negative_borel_cell_factorial_moment
        X hFinite T B hB hNeg)
  have hI : Integrable (fun ω => (J ω - r) ^ 2) P := by
    have hId : (fun ω => (J ω - r) ^ 2) =
        (fun ω => (J ω * (J ω - 1) + (1 - 2 * r) * J ω) + r ^ 2) := by
      funext ω
      ring
    rw [hId]
    exact (hFI.add (hJI.const_mul (1 - 2 * r))).add
      (integrable_const (r ^ 2))
  refine ⟨hI, ?_⟩
  calc
    (∫ ω, (J ω - r) ^ 2 ∂P) =
      ∫ ω, (J ω * (J ω - 1) + (1 - 2 * r) * J ω) + r ^ 2 ∂P := by
        congr 1
        funext ω
        ring
    _ = r := by
      have hPlus : (∫ ω, (J ω * (J ω - 1) + (1 - 2 * r) * J ω) + r ^ 2 ∂P) =
          (∫ ω, J ω * (J ω - 1) + (1 - 2 * r) * J ω ∂P) + r ^ 2 := by
        simpa [Pi.add_apply, integral_const, Measure.real] using
          (integral_add (hFI.add (hJI.const_mul (1 - 2 * r)))
            (integrable_const (r ^ 2)))
      have hInner : (∫ ω, J ω * (J ω - 1) + (1 - 2 * r) * J ω ∂P) =
          (∫ ω, J ω * (J ω - 1) ∂P) +
            (1 - 2 * r) * (∫ ω, J ω ∂P) := by
        simpa only [Pi.add_apply, integral_const_mul] using
          (integral_add hFI (hJI.const_mul (1 - 2 * r)))
      rw [hPlus, hInner, hF, hJ]
      ring
