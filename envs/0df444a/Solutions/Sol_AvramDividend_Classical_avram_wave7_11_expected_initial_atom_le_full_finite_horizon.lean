-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_11_expected_initial_atom_le_full_finite_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:58:13.877808+00:00
-- url     : https://prove2.me/submissions/d5fc13bb-39cf-49db-8baf-27e4d782c9f0

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_discounted_stieltjes_horizon_mono
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The exact original expected finite-horizon Stieltjes reward retains
    at least its complete time-zero dividend atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (D : ℝ≥0 → Ω → ℝ) (σ : Ω → ℝ≥0∞)
    (q T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, (dividendMeasure D ω) ({0} : Set ℝ) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  calc
    (∫⁻ ω, (dividendMeasure D ω) ({0} : Set ℝ) ∂P) =
      (∫⁻ ω, ∫⁻ t in paymentTimes (σ ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
          apply lintegral_congr
          intro ω
          exact (avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
            D ω (σ ω) q).symm
    _ ≤ _ := avram_wave7_11_discounted_stieltjes_horizon_mono
      D σ q 0 T hT
