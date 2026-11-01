-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_bv_actual_filtration_measurable_source_count_poisson_exact_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:33:53.306407+00:00
-- url     : https://prove2.me/submissions/52968b07-fc89-4800-88f7-9b1539b393a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_bv_actual_total_source_count_filtration_measurable_random_variable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_exact_intensity

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

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
      (∀ᵐ ω ∂P, F ω = ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ))) ∧
      (∀ k : ℕ, P.real {ω : Ω | F ω = (k : ℝ≥0∞)} = Real.exp (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) *
          ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) ^ k /
            (k.factorial : ℝ)) := by
  obtain ⟨F, hFm, hFae⟩ :=
    avram_wave5_01_bv_actual_total_source_count_filtration_measurable_random_variable
      X hBV hFinite T hT grid hGrid hMesh hBound
  refine ⟨F, hFm, hFae, ?_⟩
  intro k
  have hAe : ∀ᵐ ω ∂P,
      (F ω = (k : ℝ≥0∞) ↔ ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ℝ≥0∞)) := by
    filter_upwards [hFae] with ω hω
    rw [hω]
  have hP :
      P {ω : Ω | F ω = (k : ℝ≥0∞)} =
      P {ω : Ω | ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ℝ≥0∞)} := by
    exact measure_congr (Filter.eventuallyEq_set.mpr hAe)
  calc
    P.real {ω : Ω | F ω = (k : ℝ≥0∞)} =
      P.real {ω : Ω | ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (Set.univ : Set ℝ)) = (k : ℝ≥0∞)} :=
      congrArg ENNReal.toReal hP
    _ = Real.exp (-((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) *
          ((T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal) ^ k /
            (k.factorial : ℝ) :=
      avram_wave4_04a_bv_actual_intrinsic_jump_count_poisson_exact_intensity
        X hBV hFinite T hT k
