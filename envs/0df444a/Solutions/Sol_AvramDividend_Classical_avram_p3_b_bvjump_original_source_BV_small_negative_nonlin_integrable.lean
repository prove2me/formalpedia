-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_small_negative_nonlin_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:01:00.923123+00:00
-- url     : https://prove2.me/submissions/d688fe2b-a035-4f26-abd2-3a84b311cfc2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- BV's genuine original-source first moment controls the C1 nonlinear
integrand on the small negative jump band, without any big-tail moment. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (K : ℝ≥0) (a b u : ℝ)
    (hLip : LipschitzOnWith K w (Icc a b))
    (hu : u ∈ Icc (a + 1) b)
    (hMeas : AEStronglyMeasurable (fun z : ℝ => w (u + z) - w u)
      (X.ν.restrict (Ioo (-1 : ℝ) 0))) :
    IntegrableOn (fun z : ℝ => w (u + z) - w u)
      (Ioo (-1 : ℝ) 0) X.ν := by
  have hMoment := bv_small_negative_first_moment_integrable X hBV
  have hMomentK : Integrable (fun z : ℝ => (K : ℝ) * (-z))
      (X.ν.restrict (Ioo (-1 : ℝ) 0)) := hMoment.const_mul _
  apply Integrable.mono' hMomentK hMeas
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  have hz' : z ∈ Icc (-1 : ℝ) 0 :=
    ⟨(mem_Ioo.mp hz).1.le, (mem_Ioo.mp hz).2.le⟩
  have h := avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
    w K a b 1 u z (by norm_num) hLip hu hz'
  have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
  have hzabs : |z| = -z := abs_of_neg (mem_Ioo.mp hz).2
  simpa only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hK, hzabs]
    using h
