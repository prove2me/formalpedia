-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_f_original_physical_conditional_count_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:10:26.175858+00:00
-- url     : https://prove2.me/submissions/4275a788-c1cd-442d-8c27-1bf0cf77cb51

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_future_path_conditional_first_second_moments
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (N : Ω → ℝ≥0∞)
    (hN : ∀ ω, N ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ)
    (hInt : Integrable (fun ω => (N ω).toReal - r) P)
    (hSqInt : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P)
    (hMean : (∫ ω, (N ω).toReal - r ∂P) = 0)
    (hVariance : (∫ ω, ((N ω).toReal - r) ^ 2 ∂P) = r) :
    (P[(fun ω => (N ω).toReal - r) | 𝓕 s] =ᵐ[P] (fun _ => 0)) ∧
    (P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕 s] =ᵐ[P] (fun _ => r)) := by
  obtain ⟨F, hF, hFsource, _⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
      X s t hst B hB
  let J : (ℝ≥0 → ℝ) → ℝ := fun p => (F p).toReal - r
  have hJ : Measurable J := by
    exact (ENNReal.measurable_toReal.comp hF).sub measurable_const
  have hRep (ω : Ω) :
      J (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) =
        (N ω).toReal - r := by
    change (F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)).toReal - r =
      (N ω).toReal - r
    rw [← hFsource ω, ← hN ω]
  have hEq : (fun ω : Ω =>
      J (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) =
      (fun ω => (N ω).toReal - r) := funext hRep
  have hSqEq : (fun ω : Ω =>
      (J (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ^ 2) =
      (fun ω => ((N ω).toReal - r) ^ 2) := by
    funext ω
    rw [hRep ω]
  have hJInt : Integrable
      (fun ω => J (fun v => X.X (s + v) ω - X.X s ω)) P := by
    rw [hEq]
    exact hInt
  have hJSqInt : Integrable
      (fun ω => (J (fun v => X.X (s + v) ω - X.X s ω)) ^ 2) P := by
    rw [hSqEq]
    exact hSqInt
  obtain ⟨hFirst, hSecond⟩ :=
    avram_wave5_02b_original_future_path_conditional_first_second_moments
      X s J hJ hJInt hJSqInt
  constructor
  · simpa only [hEq, hMean] using hFirst
  · simpa only [hSqEq, hVariance] using hSecond
