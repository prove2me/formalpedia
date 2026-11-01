-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_crossing_weighted_quadratic_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:24:09.518994+00:00
-- url     : https://prove2.me/submissions/561cfbf1-d583-41fa-91a3-0b1d6676b58d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_crossing_quadratic_strip

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral Filter
open scoped NNReal ENNReal

/-- Weighted crossing-strip kernel obeys the original source O(r²) bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r θ : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) (hθ : 0 ≤ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) *
        |r * W x - ∫ t in (0 : ℝ)..x, W t|)
      (Ioo (0 : ℝ) r) volume ∧
    (∫ x in Ioo (0 : ℝ) r,
      Real.exp (-(θ*x)) *
        |r * W x - ∫ t in (0 : ℝ)..x, W t|) ≤
      W 1 * r^2 := by
  let s : Set ℝ := Ioo 0 r
  let v : ℝ → ℝ := fun x =>
    |r * W x - ∫ t in (0 : ℝ)..x, W t|
  let f : ℝ → ℝ := fun x => Real.exp (-(θ*x)) * v x
  have hI :=
    avram_wave4_p2_scale_primitive_crossing_quadratic_strip
      X q W hW r hr0 hr1
  have hExpMeas : Measurable (fun x : ℝ => Real.exp (-(θ*x))) := by
    fun_prop
  have hFm : AEStronglyMeasurable f (volume.restrict s) :=
    hExpMeas.aestronglyMeasurable.mul hI.1.aestronglyMeasurable
  have hpoint : ∀ x ∈ s, f x ≤ v x := by
    intro x hx
    have he : Real.exp (-(θ*x)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [mul_nonneg hθ (le_of_lt hx.1)]
    have hv : 0 ≤ v x := abs_nonneg _
    dsimp [f]
    nlinarith [Real.exp_nonneg (-(θ*x))]
  have hFint : IntegrableOn f s volume := by
    apply Integrable.mono hI.1 hFm
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hfx : 0 ≤ f x :=
      mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
    have hvx : 0 ≤ v x := abs_nonneg _
    change |f x| ≤ |v x|
    rw [abs_of_nonneg hfx, abs_of_nonneg hvx]
    exact hpoint x hx
  refine ⟨hFint, ?_⟩
  calc
    (∫ x in s, f x) ≤ ∫ x in s, v x :=
      setIntegral_mono_on hFint hI.1 measurableSet_Ioo hpoint
    _ ≤ W 1 * r^2 := hI.2
