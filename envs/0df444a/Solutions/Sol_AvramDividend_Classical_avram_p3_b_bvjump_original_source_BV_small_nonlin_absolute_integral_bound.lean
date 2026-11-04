-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_small_nonlin_absolute_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:17:16.927201+00:00
-- url     : https://prove2.me/submissions/06ee1097-8be9-4002-8495-b735527fafcf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- Original BV source small-jump nonlinear absolute integral is bounded
uniformly on a compact interior by its finite first negative-jump moment. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (K : ℝ≥0) (a b u : ℝ)
    (hLip : LipschitzOnWith K w (Icc a b))
    (hu : u ∈ Icc (a + 1) b) :
    (∫ z in Ioo (-1 : ℝ) 0, |w (u + z) - w u| ∂X.ν) ≤
      (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν) := by
  let μ := X.ν.restrict (Ioo (-1 : ℝ) 0)
  have hMoment : Integrable (fun z : ℝ => -z) μ :=
    bv_small_negative_first_moment_integrable X hBV
  have hMomentK : Integrable (fun z : ℝ => (K : ℝ) * (-z)) μ :=
    hMoment.const_mul _
  have hInc : Integrable (fun z : ℝ => w (u + z) - w u) μ :=
    avram_p3_b_bvjump_original_source_BV_small_nonlin_L1_of_local_Lipschitz
      X hBV w K a b u hLip hu
  have hAbs : Integrable (fun z : ℝ => |w (u + z) - w u|) μ := by
    simpa only [Real.norm_eq_abs] using hInc.norm
  have hAE : ∀ᵐ z ∂μ,
      |w (u + z) - w u| ≤ (K : ℝ) * (-z) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hz' : z ∈ Icc (-1 : ℝ) 0 :=
      ⟨(mem_Ioo.mp hz).1.le, (mem_Ioo.mp hz).2.le⟩
    have h := avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
      w K a b 1 u z (by norm_num) hLip hu hz'
    simpa only [abs_of_neg (mem_Ioo.mp hz).2] using h
  have h := integral_mono_ae hAbs hMomentK hAE
  simpa only [integral_const_mul] using h
