-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_discounted_rightjump_residual_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:26:34.001652+00:00
-- url     : https://prove2.me/submissions/757f6de4-e491-4a56-b587-1d3170e3a805

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original discounted right-payment minus its secant value loss is nonpositive. -/
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
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) -
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))) ≤ 0 := by
  have hbase := hjump ω t ht
  have hres : (rightLimit D t ω - D t ω) -
      (w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω))) ≤ 0 :=
    sub_nonpos.mpr hbase
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) hres

