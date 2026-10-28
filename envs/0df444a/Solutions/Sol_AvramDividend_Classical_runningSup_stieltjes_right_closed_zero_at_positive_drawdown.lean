-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stieltjes_right_closed_zero_at_positive_drawdown
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:54:44.398684+00:00
-- url     : https://prove2.me/submissions/3c3be6b8-834d-46d9-904e-c3d928f231e2

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Theorems.Thm_AvramDividend_Classical_runningSup_stieltjes_right_interval_zero_at_positive_drawdown
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_real_atoms

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0)
    (hPositive : 0 < reflectedSup X u ω) :
    ∃ v : ℝ≥0, u < v ∧
      (dividendMeasure (runningSup X) ω)
        (Set.Icc (u : ℝ) (v : ℝ)) = 0 := by
  obtain ⟨v, huv, hv⟩ :=
    AvramDividend.Classical.runningSup_stieltjes_right_interval_zero_at_positive_drawdown X ω u hPositive
  refine ⟨v, huv, ?_⟩
  have hle : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv.le
  rw [← Set.Icc_union_Ioc_eq_Icc le_rfl hle, Set.Icc_self]
  apply le_antisymm _ (zero_le)
  calc _ ≤ (dividendMeasure (runningSup X) ω) {(u : ℝ)} +
        (dividendMeasure (runningSup X) ω) (Set.Ioc (u : ℝ) (v : ℝ)) := measure_union_le _ _
    _ = 0 := by rw [AvramDividend.Classical.runningSup_dividendMeasure_no_real_atoms, hv, add_zero]
