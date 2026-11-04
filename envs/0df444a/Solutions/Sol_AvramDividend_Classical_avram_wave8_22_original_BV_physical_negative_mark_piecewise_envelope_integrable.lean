-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_physical_negative_mark_piecewise_envelope_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:36:45.365856+00:00
-- url     : https://prove2.me/submissions/d063eed0-3b45-41c2-865e-f4c917b63bba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_small_negative_first_moment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original BV negative Lévy measure integrates the compact C¹
piecewise near-linear and far-constant jump envelope. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (a L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
  (hL : 0 ≤ L) (hR : 0 ≤ R) :
  IntegrableOn (fun z : ℝ => if z ≤ -a / 2 then 2 * R else L * (-z))
    (Iio (0 : ℝ)) X.ν := by
  let G : ℝ → ℝ := fun z => if z ≤ -a / 2 then 2 * R else L * (-z)
  have hGmeas : Measurable G := by
    change Measurable (fun z : ℝ => if z ∈ Iic (-a / 2) then 2 * R else L * (-z))
    exact (measurable_const : Measurable (fun _ : ℝ => 2 * R)).ite
      measurableSet_Iic (measurable_const.mul measurable_id.neg)
  have hSub : Ioo (-a / 2) (0 : ℝ) ⊆ Ioo (-1) 0 := by
    intro z hz
    exact ⟨by linarith [hz.1, ha2], hz.2⟩
  have hFirst : IntegrableOn (fun z : ℝ => -z) (Ioo (-a / 2) 0) X.ν :=
    (bv_small_negative_first_moment_integrable X hBV).mono_set hSub
  have hNear : IntegrableOn G (Ioo (-a / 2) 0) X.ν := by
    apply (hFirst.const_mul L).mono' hGmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hcut : ¬ z ≤ -a / 2 := not_le.mpr hz.1
    have hpos : 0 ≤ L * (-z) := mul_nonneg hL (by linarith [hz.2])
    simpa only [G, if_neg hcut, Real.norm_eq_abs, abs_of_nonneg hpos] using
      (le_refl (L * (-z)))
  have hMass : X.ν (Iic (-a / 2)) < ⊤ :=
    avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
      X a ha ha2
  have hFar : IntegrableOn G (Iic (-a / 2)) X.ν := by
    apply IntegrableOn.of_bound hMass hGmeas.aestronglyMeasurable (2 * R)
    filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
    have hpos : 0 ≤ 2 * R := by positivity
    have hcut : z ≤ -a / 2 := hz
    have hEval : G z = 2 * R := by simp [G, hcut]
    simpa only [hEval, Real.norm_eq_abs, abs_of_nonneg hpos] using
      (le_refl (2 * R))
  have hCover : Iic (-a / 2) ∪ Ioo (-a / 2) (0 : ℝ) = Iio 0 := by
    ext z
    simp only [mem_union, mem_Iic, mem_Ioo, mem_Iio]
    constructor
    · intro hz
      rcases hz with hz | ⟨_, hz⟩
      · exact lt_of_le_of_lt hz (by linarith)
      · exact hz
    · intro hz
      by_cases hcut : z ≤ -a / 2
      · exact Or.inl hcut
      · exact Or.inr ⟨lt_of_not_ge hcut, hz⟩
  change IntegrableOn G (Iio 0) X.ν
  rw [← hCover]
  exact hFar.union hNear
