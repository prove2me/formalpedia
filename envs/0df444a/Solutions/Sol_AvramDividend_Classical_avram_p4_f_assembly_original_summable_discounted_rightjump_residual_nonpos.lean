-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_summable_discounted_rightjump_residual_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:26:41.641867+00:00
-- url     : https://prove2.me/submissions/438e0612-f876-4660-9a3b-23381ffbbce0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The summable original discounted right-payment residual has nonpositive total. -/
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
    (ω : Ω) (A : Set ℝ≥0)
    (helig : ∀ t ∈ A, t = 0 ∨
      (t : ℝ≥0∞) < ruinTime X x D ω)
    (R : A → ℝ)
    (hR : ∀ a : A, R a =
      Real.exp (-(q * (a.1 : ℝ))) *
        ((rightLimit D a.1 ω - D a.1 ω) -
          (w (riskProcess X x D a.1 ω) -
            w (riskProcess X x D a.1 ω -
              (rightLimit D a.1 ω - D a.1 ω)))))
    (hSum : Summable R) :
    (∑' a : A, R a) ≤ 0 := by
  have hpoint : ∀ a : A, R a ≤ 0 := by
    intro a
    rw [hR a]
    have hbase := hjump ω a.1 (helig a.1 a.2)
    have hres : (rightLimit D a.1 ω - D a.1 ω) -
        (w (riskProcess X x D a.1 ω) -
          w (riskProcess X x D a.1 ω -
            (rightLimit D a.1 ω - D a.1 ω))) ≤ 0 :=
      sub_nonpos.mpr hbase
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos _)) hres
  first
  | exact tsum_nonpos hpoint hSum
  | exact tsum_nonpos hSum hpoint
  | exact tsum_nonpos hpoint

