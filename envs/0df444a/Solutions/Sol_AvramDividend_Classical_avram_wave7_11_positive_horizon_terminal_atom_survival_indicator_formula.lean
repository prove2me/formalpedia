-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_positive_horizon_terminal_atom_survival_indicator_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:01:32.005205+00:00
-- url     : https://prove2.me/submissions/cfb7d0a0-51ab-4880-ad5f-f405c616193f

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_positive_terminal_stieltjes_atom_exact_survival
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_no_terminal_payment_if_clock_ended
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact positive-horizon terminal dividend Stieltjes atom:
    the discounted singleton survives precisely while the original
    strict ruin clock is later than the observation instant. -/
theorem solution
    {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (σ : ℝ≥0∞) (q T : ℝ) (hT : 0 < T) :
    (∫⁻ t in (paymentTimes σ ∩ Iic T) ∩ {T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      if ENNReal.ofReal T < σ then
        (dividendMeasure D ω) ({T} : Set ℝ) *
          ENNReal.ofReal (Real.exp (-(q * T)))
      else 0 := by
  by_cases hsurv : ENNReal.ofReal T < σ
  · rw [if_pos hsurv]
    exact avram_wave7_11_positive_terminal_stieltjes_atom_exact_survival
      D ω σ q T hT hsurv
  · have hstop : σ ≤ ENNReal.ofReal T := le_of_not_gt hsurv
    have hno : paymentTimes σ ∩ ({T} : Set ℝ) = ∅ :=
      avram_wave7_11_no_terminal_payment_if_clock_ended σ T hT hstop
    have hempty : (paymentTimes σ ∩ Iic T) ∩ ({T} : Set ℝ) = ∅ := by
      apply Set.Subset.antisymm
      · intro t ht
        have htno : t ∈ paymentTimes σ ∩ ({T} : Set ℝ) :=
          ⟨ht.1.1, ht.2⟩
        rw [hno] at htno
        exact htno
      · exact Set.empty_subset _
    simp [hsurv, hempty]
