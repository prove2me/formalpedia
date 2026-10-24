-- Prove2me | solution 1 for AvramDividend.Classical.dividendMeasure_paymentWindow_finite_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:07:57.930245+00:00
-- url     : https://prove2.me/submissions/d91a2524-9ec7-426c-8ce8-1ad3a686a1e1

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Mathlib.Tactic.NormNum
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Stopped payment times up to a finite horizon have finite Stieltjes mass:
    enlarge their window to [0,T+1) and use the cumulative-dividend identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0) :
    dividendMeasure D ω (paymentTimes σ ∩ Iic (T : ℝ)) ≠ ⊤ := by
  have hTsucc : (T : ℝ) < ((T + 1 : ℝ≥0) : ℝ) := by
    exact_mod_cast
      (lt_add_of_pos_right T (by norm_num : (0 : ℝ≥0) < 1))
  have hsubset :
      paymentTimes σ ∩ Iic (T : ℝ) ⊆
        Ico (0 : ℝ) ((T + 1 : ℝ≥0) : ℝ) := by
    intro t ht
    exact ⟨ht.1.1, lt_of_le_of_lt ht.2 hTsucc⟩
  have hmass := measure_mono (μ := dividendMeasure D ω) hsubset
  rw [dividendMeasure_Ico_zero_eq_dividendValue D hD ω (T + 1)] at hmass
  have hfin : ENNReal.ofReal (D (T + 1) ω) < ⊤ := by simp
  exact (lt_of_le_of_lt hmass hfin).ne
