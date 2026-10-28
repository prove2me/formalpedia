-- Prove2me | solution 2 for AvramDividend.Classical.barrierRuinTime_zero_eq_iInf_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T09:38:06.808403+00:00
-- url     : https://prove2.me/submissions/2ebe9030-9ae8-4776-ab48-ddc3fed3f551

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_eq_iInf_positive
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    barrierRuinTime X 0 ω =
      ⨅ n : ℕ, barrierRuinTime X (1 / ((n : ℝ) + 1)) ω := by
  rw [AvramDividend.Classical.barrierRuinTime_zero_eq_iInf_positive]
  apply le_antisymm
  · exact le_iInf fun n => iInf₂_le (1 / ((n : ℝ) + 1)) (by positivity)
  · refine le_iInf₂ fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact (iInf_le _ n).trans
      (AvramDividend.Classical.barrierRuinTime_mono_barrier X _ _ hn.le ω)
