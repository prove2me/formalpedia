-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_negative_levy_small_first_moment_large_finite_piecewise_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:57:03.921772+00:00
-- url     : https://prove2.me/submissions/86952d9d-1aff-49c8-ae25-bbe85a84b9da

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- An original BV Lévy negative-mark envelope uses first variation near
zero and only finite mark intensity away from zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (a L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hMass : X.ν (Iic (-a / 2)) < ⊤) :
    IntegrableOn (fun z : ℝ =>
      if z ≤ -a / 2 then 2 * R else L * (-z))
      (Iio 0) X.ν := by
  let g : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z)
  change IntegrableOn g (Iio 0) X.ν
  have hMeas : Measurable g := by
    change Measurable (fun z : ℝ =>
      if z ≤ -a / 2 then 2 * R else L * (-z))
    have hs : MeasurableSet {z : ℝ | z ≤ -a / 2} := measurableSet_Iic
    exact Measurable.ite hs measurable_const (measurable_const.mul measurable_id.neg)
  have hSub : Ioo (-a / 2) (0 : ℝ) ⊆ Ioo (-1) 0 := by
    intro z hz
    exact ⟨by linarith [hz.1, ha2], hz.2⟩
  have hSmall : IntegrableOn (fun z : ℝ => L * (-z))
      (Ioo (-a / 2) 0) X.ν :=
    ((bv_small_negative_first_moment_integrable X hBV).mono_set hSub).const_mul L
  have hGsmall : IntegrableOn g (Ioo (-a / 2) 0) X.ν := by
    apply hSmall.congr
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
    have hznot : ¬ z ≤ -a / 2 := not_le.mpr hz.1
    change L * (-z) = g z
    simp only [g, if_neg hznot]
  have hGlarge : IntegrableOn g (Iic (-a / 2)) X.ν := by
    apply MeasureTheory.IntegrableOn.of_bound hMass
      hMeas.aestronglyMeasurable (2 * R)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with z hz
    have hzle : z ≤ -a / 2 := hz
    have hval : g z = 2 * R := by simp only [g, if_pos hzle]
    rw [hval]
    change |(2 : ℝ) * R| ≤ 2 * R
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hR)]
  have hCover : Iic (-a / 2) ∪ Ioo (-a / 2) (0 : ℝ) = Iio 0 := by
    ext z
    simp only [mem_union, mem_Iic, mem_Ioo, mem_Iio]
    constructor
    · intro hz
      rcases hz with hz | ⟨_, hz⟩
      · have hcut : -a / 2 < (0 : ℝ) := by linarith
        exact lt_of_le_of_lt hz hcut
      · exact hz
    · intro hz
      by_cases hcut : z ≤ -a / 2
      · exact Or.inl hcut
      · exact Or.inr ⟨lt_of_not_ge hcut, hz⟩
  rw [← hCover]
  exact hGlarge.union hGsmall
