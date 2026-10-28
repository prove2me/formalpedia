-- Prove2me | solution 1 for AvramDividend.Classical.bv_esscher_positive_tail_kernel_diverges_of_levy_activity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T09:50:39.711496+00:00
-- url     : https://prove2.me/submissions/5f1a7700-a98d-4693-a8f4-38ed2a9a85aa

import Theorems.Thm_AvramDividend_Classical_bv_esscher_positive_tail_kernel_shape_of_root
import Theorems.Thm_AvramDividend_Classical_esscher_positive_magnitude_tail_real_tendsto_top
import Theorems.Thm_AvramDividend_Classical_negative_jump_real_tail_tendsto_top
import Theorems.Thm_AvramDividend_Classical_negative_jump_truncation_measure_finite
import Mathlib.MeasureTheory.Measure.WithDensity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- Keep the canonical BV Esscher kernel and prove its origin divergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hνint : ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν < ⊤)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤) :
    ∃ κ : ℝ → ℝ,
      (∀ t : ℝ, κ t = if 0 < t then
        ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
          (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
          {z : ℝ≥0 | t < (z : ℝ)}) else 0) ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, t ≤ 0 → κ t = 0) ∧
      (∀ t : ℝ, 0 ≤ κ t) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      Tendsto κ (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  have hfar : X.ν (Iic (-1 : ℝ)) < ⊤ :=
    negative_jump_truncation_measure_finite X.ν hνint 1 zero_lt_one
  have hfinite : ∀ x : ℝ, 0 < x → X.ν (Iio (-x)) < ⊤ := by
    intro x hx
    have hsub : Iio (-x) ⊆ Iic (-x) := by
      intro y hy
      exact le_of_lt (by simpa only [mem_Iio] using hy)
    exact lt_of_le_of_lt (measure_mono hsub)
      (negative_jump_truncation_measure_finite X.ν hνint x hx)
  have htail := negative_jump_real_tail_tendsto_top X.ν hνint hνinf
  have hpositive := esscher_positive_magnitude_tail_real_tendsto_top
    X.ν φ hφ.le hfar hfinite htail
  obtain ⟨κ, hκ, hcont, hanti, hzero, hnonneg, hint⟩ :=
    bv_esscher_positive_tail_kernel_shape_of_root X hX hbv q hq φ hφ hroot
  refine ⟨κ, hκ, hcont, hanti, hzero, hnonneg, hint, ?_⟩
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards [(tendsto_atTop.1 hpositive) M, self_mem_nhdsWithin]
    with x hx hxpos
  have hxgt : 0 < x := by simpa only [mem_Ioi] using hxpos
  simpa only [hκ x, if_pos hxgt] using hx
