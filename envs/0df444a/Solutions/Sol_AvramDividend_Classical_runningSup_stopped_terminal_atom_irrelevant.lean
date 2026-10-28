-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_terminal_atom_irrelevant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:29:02.893848+00:00
-- url     : https://prove2.me/submissions/d8dd0a11-5b42-4897-8319-1cd8689e2910

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_positive_atoms
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_atom
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- With no running-record Stieltjes jump at a nonnegative terminal time, excluding
the endpoint does not alter any nonnegative weighted dividend reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T : ℝ) (hT : 0 ≤ T) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc (0 : ℝ) T, f t
      ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ t in Ioo (0 : ℝ) T, f t
      ∂(dividendMeasure (runningSup X) ω)) := by
  let μ := dividendMeasure (runningSup X) ω
  have hatom : μ ({T} : Set ℝ) = 0 := by
    rcases eq_or_lt_of_le hT with hz | hpos
    · subst T
      exact runningSup_dividendMeasure_zero_atom X ω
    · exact runningSup_dividendMeasure_no_positive_atoms X ω T hpos
  exact setLIntegral_congr (Ioo_ae_eq_Ioc' hatom).symm
