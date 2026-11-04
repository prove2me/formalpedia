-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_discounted_cash_atom_le_value_loss
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:36:29.327722+00:00
-- url     : https://prove2.me/submissions/17a48479-4679-4ca1-9044-81fae83dbaee

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual discounted Cash atom is bounded by the original value secant loss. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ (ω : Ω) (t : ℝ≥0),
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω →
        rightLimit D t ω - D t ω ≤
          w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0) (μatom : Measure ℝ)
    (hμatom : μatom {(t : ℝ)} =
      ENNReal.ofReal (rightLimit D t ω - D t ω))
    (hdelta : 0 ≤ rightLimit D t ω - D t ω)
    (helig : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (ENNReal.ofReal (Real.exp (-(q * (t : ℝ)))) *
      μatom {(t : ℝ)}).toReal ≤
      Real.exp (-(q * (t : ℝ))) *
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) := by
  rw [avram_p4_f_assembly_original_cash_atom_toReal_eq_discounted_rightjump
    D ω q t μatom hμatom hdelta]
  exact mul_le_mul_of_nonneg_left (hjump ω t helig)
    (le_of_lt (Real.exp_pos _))
