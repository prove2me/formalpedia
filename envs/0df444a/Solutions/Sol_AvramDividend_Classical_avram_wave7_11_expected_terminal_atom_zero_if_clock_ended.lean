-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_expected_terminal_atom_zero_if_clock_ended
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:22:03.13077+00:00
-- url     : https://prove2.me/submissions/9fe9ad81-c3a8-401a-9cd6-0c79ccdddae8

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_no_terminal_payment_if_clock_ended
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Expected original terminal dividend-atom reward vanishes when
    every original sample clock has stopped by the positive horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (T : ℝ) (hT : 0 < T)
    (hσ : ∀ ω, σ ω ≤ ENNReal.ofReal T) (q : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) = 0 := by
  have hpoint (ω : Ω) :
      (∫⁻ t in paymentTimes (σ ω) ∩ {T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 := by
    rw [avram_wave7_11_no_terminal_payment_if_clock_ended
      (σ ω) T hT (hσ ω)]
    simp
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) =
        ∫⁻ _ω, (0 : ℝ≥0∞) ∂P := by
          congr 1
          funext ω
          exact hpoint ω
    _ = 0 := by simp
