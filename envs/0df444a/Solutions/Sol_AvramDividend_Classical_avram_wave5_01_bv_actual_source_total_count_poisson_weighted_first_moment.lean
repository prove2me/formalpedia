-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_source_total_count_poisson_weighted_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:22:40.643558+00:00
-- url     : https://prove2.me/submissions/849e00cb-32bb-4d8f-a0c7-33e5574ab0fb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV jump-count proxy has the exact weighted Poisson mass sum,
equal to its genuine Lévy total-negative-mark intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T)
    (grid : ℕ → ℕ → ℝ≥0)
    (hGrid : ∀ n : ℕ, 0 < n →
      StrictMono (grid n) ∧ grid n 0 = 0 ∧ grid n n = T)
    (hMesh : ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, ∀ i : ℕ, i < n →
        dist (grid n i) (grid n (i + 1)) < δ)
    (hBound : ∀ n i : ℕ, i ≤ n → grid n i ≤ T) :
    ∃ F : Ω → ℝ≥0∞, Measurable[𝓕 T] F ∧
      (∀ᵐ ω ∂P,
        F ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim
            (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) ∧
      (∑' k : ℕ,
        (k : ℝ) * P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) =
        (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by
  obtain ⟨F, hFm, hFae, hFLaw⟩ :=
    avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
      X hBV hFinite T hT grid hGrid hMesh hBound
  refine ⟨F, hFm, hFae, ?_⟩
  let r : ℝ≥0 :=
    ⟨(T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal,
      mul_nonneg (NNReal.coe_nonneg T) ENNReal.toReal_nonneg⟩
  have hr : (r : ℝ) = (T : ℝ) *
      (X.ν (Iio (0 : ℝ))).toReal := rfl
  have hPMF (k : ℕ) :
      P.real {ω : Ω | F ω = (k : ℝ≥0∞)} =
        (ProbabilityTheory.poissonMeasure r).real {k} := by
    rw [hFLaw k, ProbabilityTheory.poissonMeasure_real_singleton]
    rfl
  have hMean :
      (∑' k : ℕ,
        (k : ℝ) * (ProbabilityTheory.poissonMeasure r).real {k}) =
        (r : ℝ) := by
    calc
      _ = ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r) := by
        rw [ProbabilityTheory.integral_poissonMeasure]
        apply tsum_congr
        intro k
        rw [ProbabilityTheory.poissonMeasure_real_singleton]
        ring
      _ = (r : ℝ) := poisson_count_expected_rate_ws01b r
  calc
    (∑' k : ℕ, (k : ℝ) *
      P.real {ω : Ω | F ω = (k : ℝ≥0∞)}) =
        ∑' k : ℕ, (k : ℝ) *
          (ProbabilityTheory.poissonMeasure r).real {k} := by
      apply tsum_congr
      intro k
      rw [hPMF k]
    _ = (r : ℝ) := hMean
    _ = (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := hr
