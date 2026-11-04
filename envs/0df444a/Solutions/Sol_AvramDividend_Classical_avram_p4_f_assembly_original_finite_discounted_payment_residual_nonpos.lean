-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_finite_discounted_payment_residual_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:26:37.924085+00:00
-- url     : https://prove2.me/submissions/65306347-252b-49cd-9a7f-bf747f408afa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite sums of true discounted dividend-minus-secant residuals are nonpositive. -/
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
    (ω : Ω) (S : Finset ℝ≥0)
    (helig : ∀ t ∈ S,
      t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    (∑ t ∈ S, Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) -
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro t ht
  have hbase := hjump ω t (helig t ht)
  have hres : (rightLimit D t ω - D t ω) -
      (w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω))) ≤ 0 :=
    sub_nonpos.mpr hbase
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) hres

