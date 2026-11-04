-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_source_BV_variable_cutoff_nonlin_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:57:22.145212+00:00
-- url     : https://prove2.me/submissions/1749d19a-3904-43d0-b458-5c3c57ff5a81

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

/-- The actual BV Levy measure controls nonlinear increments on every
positive small-jump cut-off, with exactly that cut-off's interior margin. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (K : ℝ≥0) (a b δ u : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hLip : LipschitzOnWith K w (Icc a b))
    (hu : u ∈ Icc (a + δ) b) :
    IntegrableOn (fun z : ℝ => w (u + z) - w u)
      (Ioo (-δ) 0) X.ν := by
  have hsubset : Ioo (-δ) 0 ⊆ Ioo (-1 : ℝ) 0 := by
    intro z hz
    rcases hz with ⟨hzlo, hzhi⟩
    exact ⟨by linarith, hzhi⟩
  have hmoment : Integrable (fun z : ℝ => -z)
      (X.ν.restrict (Ioo (-δ) 0)) :=
    (bv_small_negative_first_moment_integrable X hBV).mono_set hsubset
  have hbound : Integrable (fun z : ℝ => (K : ℝ) * (-z))
      (X.ν.restrict (Ioo (-δ) 0)) := hmoment.const_mul _
  have hmap : MapsTo (fun z : ℝ => u + z) (Ioo (-δ) 0) (Icc a b) := by
    intro z hz
    rcases hu with ⟨hlo, hhi⟩
    rcases hz with ⟨hzlo, hzhi⟩
    exact ⟨by linarith, by linarith⟩
  have hcont : ContinuousOn (fun z : ℝ => w (u + z) - w u)
      (Ioo (-δ) 0) := by
    have hcomp : ContinuousOn (fun z : ℝ => w (u + z))
        (Ioo (-δ) 0) :=
      hLip.continuousOn.comp
        ((continuous_const.add continuous_id).continuousOn) hmap
    exact hcomp.sub continuousOn_const
  have hmeas : AEStronglyMeasurable (fun z : ℝ => w (u + z) - w u)
      (X.ν.restrict (Ioo (-δ) 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  apply Integrable.mono' hbound hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  have hz' : z ∈ Icc (-δ) 0 :=
    ⟨(mem_Ioo.mp hz).1.le, (mem_Ioo.mp hz).2.le⟩
  have h := avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
    w K a b δ u z hδ.le hLip hu hz'
  have hK : 0 ≤ (K : ℝ) := NNReal.coe_nonneg K
  have hzabs : |z| = -z := abs_of_neg (mem_Ioo.mp hz).2
  simpa only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hK, hzabs]
    using h
