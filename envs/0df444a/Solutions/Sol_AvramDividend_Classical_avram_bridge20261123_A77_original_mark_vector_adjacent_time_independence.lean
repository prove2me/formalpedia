-- Prove2me | solution 1 for AvramDividend.Classical.avram_bridge20261123_A77_original_mark_vector_adjacent_time_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:20:49.439267+00:00
-- url     : https://prove2.me/submissions/4fdc2618-fda5-4786-807f-26cf92fa2bdb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
import Theorems.Thm_AvramDividend_Classical_avram_bridge20261123_A77_original_finite_mark_vector_future_independent_past
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (n : ℕ)
    (B : Fin n → Set ℝ) (hB : ∀ i, MeasurableSet (B i)) :
    IndepFun
      (fun ω : Ω => fun i : Fin n =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ B i))
      (fun ω : Ω => fun i : Fin n =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s (s + T) ×ˢ B i)) P := by
  classical
  have hPastMeas (i : Fin n) :
      Measurable[𝓕 s] (fun ω : Ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ B i)) := by
    exact avram_a28_original_physical_Borel_cell_count_filtration_measurable_20261116
      X 0 s (B i) (hB i)
  have hPastVector : Measurable[𝓕 s]
      (fun ω : Ω => fun i : Fin n =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 s ×ˢ B i)) := by
    letI : MeasurableSpace Ω := 𝓕 s
    exact measurable_pi_lambda _ (fun i => hPastMeas i)
  exact avram_bridge20261123_A77_original_finite_mark_vector_future_independent_past
    X s T n B hB _ hPastVector
