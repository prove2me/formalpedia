-- Prove2me | solution 2 for AvramDividend.Classical.runningSup_discountedReward_antitone_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:08:20.147734+00:00
-- url     : https://prove2.me/submissions/c0112536-489f-4b77-9c4a-bb1a36b8e719

import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (q : ℝ) :
    Antitone (fun n : ℕ =>
      ∫⁻ t in paymentTimes
        (barrierRuinTime X (1 / ((n : ℝ) + 1)) ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (runningSup X) ω)) := by
  intro n m hnm
  have hle : (1 : ℝ) / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hτ := AvramDividend.Classical.barrierRuinTime_mono_barrier X _ _ hle ω
  refine lintegral_mono_set fun t ht => ⟨ht.1, ht.2.imp id fun h => h.trans_le hτ⟩
