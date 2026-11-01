-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_zero_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:25:41.936527+00:00
-- url     : https://prove2.me/submissions/656ca7be-8602-46a0-b785-ce252d9751a1

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- The oriented scale primitive has genuine support on nonnegative reserves. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : x ≤ 0) :
    (∫ t in (0 : ℝ)..x, W t) = 0 := by
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),
      t ∈ uIoc (0 : ℝ) x → W t = 0 := by
    filter_upwards [(volume : Measure ℝ).ae_ne (0 : ℝ)] with t ht hmem
    have hm : t ∈ Ioc x (0 : ℝ) := by
      simpa only [uIoc_of_ge hx] using hmem
    have htlt : t < 0 := lt_of_le_of_ne hm.2 ht
    exact hW.1 t htlt
  rw [intervalIntegral.integral_congr_ae hae]
  simp
