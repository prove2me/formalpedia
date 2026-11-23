-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_finite_mark_vector_future_independent_past
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:13:38.915813+00:00
-- url     : https://prove2.me/submissions/bdcc9ae9-1bc7-49c8-8d94-a10f089e2972

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
import Theorems.Thm_AvramDividend_Classical_actual_levy_past_indep_measurable_future_jump_family_ws01b
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    IndepFun H (fun ω : Ω => fun i : Fin n =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B i)) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hEach (i : Fin n) :
      ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
        Measurable F ∧
        ∀ ω : Ω,
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc s (s + T) ×ˢ B i) =
          F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) := by
    obtain ⟨F, hF, hEq, _⟩ :=
      avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
        X s (s + T) (by exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ T))
        (B i) (hB i)
    exact ⟨F, hF, hEq⟩
  choose F hMeasF hEq using hEach
  have hVectorMeas : Measurable
      (fun path : ℝ≥0 → ℝ => fun i : Fin n => F i path) := by
    exact measurable_pi_lambda _ hMeasF
  have hIndep :=
    actual_levy_past_indep_measurable_future_jump_family_ws01b
      X s H hH (fun path : ℝ≥0 → ℝ => fun i : Fin n => F i path)
      hVectorMeas
  convert hIndep using 1
  funext ω i
  exact hEq i ω
