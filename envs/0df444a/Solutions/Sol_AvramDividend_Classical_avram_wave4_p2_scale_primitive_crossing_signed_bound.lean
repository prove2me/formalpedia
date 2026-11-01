-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_crossing_signed_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:11:29.427999+00:00
-- url     : https://prove2.me/submissions/76357f11-239a-4f67-87eb-8b27f86709c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Small negative-jump crossing contribution for the integrated source scale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r x : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hx0 : 0 < x) (hxr : x < r) :
    0 ≤ r * W x - ∫ t in (0 : ℝ)..x, W t ∧
      r * W x - ∫ t in (0 : ℝ)..x, W t ≤ r * W 1 := by
  obtain ⟨_, hnonneg, hcont, hmono, _⟩ := hW
  have hx0le : (0 : ℝ) ≤ x := le_of_lt hx0
  have hx1 : x ≤ 1 := (le_of_lt hxr).trans hr1
  have hsegment : ContinuousOn W (uIcc (0 : ℝ) x) := by
    rw [uIcc_of_le hx0le]
    exact hcont.mono (by
      intro z hz
      exact hz.1)
  have hwi : IntervalIntegrable W volume (0 : ℝ) x :=
    hsegment.intervalIntegrable
  have hbound : ∀ t ∈ Icc (0 : ℝ) x, W t ≤ W x := by
    intro t ht
    exact hmono ht.1 hx0le ht.2
  have hupper : (∫ t in (0 : ℝ)..x, W t) ≤ x * W x := by
    have hp : (∫ t in (0 : ℝ)..x, W t) ≤
        ∫ t in (0 : ℝ)..x, (fun _ : ℝ => W x) t :=
      intervalIntegral.integral_mono_on hx0le hwi
        (intervalIntegrable_const) hbound
    simpa using hp
  have hlower : 0 ≤ ∫ t in (0 : ℝ)..x, W t := by
    apply intervalIntegral.integral_nonneg hx0le
    intro t ht
    exact hnonneg t ht.1
  have hxW : 0 ≤ W x := hnonneg x hx0le
  have hW1 : W x ≤ W 1 :=
    hmono hx0le (by norm_num : (0 : ℝ) ≤ 1) hx1
  have hmulx : x * W x ≤ r * W x :=
    mul_le_mul_of_nonneg_right (le_of_lt hxr) hxW
  have hmul1 : r * W x ≤ r * W 1 :=
    mul_le_mul_of_nonneg_left hW1 (le_of_lt hr0)
  constructor <;> linarith
