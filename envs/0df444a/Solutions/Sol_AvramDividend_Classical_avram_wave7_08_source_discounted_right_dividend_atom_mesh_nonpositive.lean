-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_08_source_discounted_right_dividend_atom_mesh_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:38:36.074446+00:00
-- url     : https://prove2.me/submissions/a9f6caa4-baf7-4d9b-8e15-34c16a779f4d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (N : ℕ) (clock : Fin N → ℝ≥0) (ω : Ω)
    (hclock : ∀ i, clock i = 0 ∨
      (clock i : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ i : Fin N,
      Real.exp (-(q * (clock i : ℝ))) *
        ((rightLimit D (clock i) ω - D (clock i) ω) -
         (w (riskProcess X x D (clock i) ω) -
          w (riskProcess X x D (clock i) ω -
            (rightLimit D (clock i) ω - D (clock i) ω))))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro i hi
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact le_of_lt (Real.exp_pos _)
  · exact sub_nonpos.mpr (hjump ω (clock i) (hclock i))
