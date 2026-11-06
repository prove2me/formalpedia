-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_interval_f_original_rightcont_physical_conditional_count_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:27:07.209845+00:00
-- url     : https://prove2.me/submissions/09dd720f-27a5-466d-b96f-33dcf16f4901

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_f_original_physical_conditional_count_moments
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
    (P[(fun ω => (N ω).toReal - r) | 𝓕.rightCont s] =ᵐ[P] (fun _ => 0)) ∧
    (P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕.rightCont s] =ᵐ[P] (fun _ => r)) := by
  obtain ⟨Y, hYX, hc, hσ, hν⟩ :=
    avram_wave5_04_source_rightCont_levy_lift X
  have hNY : ∀ ω, N ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ Y.X u ω -
          Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          Y.X u ω - Function.leftLim (fun v : ℝ≥0 => Y.X v ω) u)))
        (Ioc s t ×ˢ B) := by
    intro ω
    simpa only [hYX] using hN ω
  exact avram_p4_s3_interval_f_original_physical_conditional_count_moments
    Y s t hst B hB N hNY r hInt hSqInt hMean hVariance
