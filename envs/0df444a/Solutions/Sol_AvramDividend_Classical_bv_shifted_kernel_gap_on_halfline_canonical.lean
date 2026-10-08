-- Prove2me | solution 1 for AvramDividend.Classical.bv_shifted_kernel_gap_on_halfline_canonical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T07:16:37.570631+00:00
-- url     : https://prove2.me/submissions/00030557-f64a-4fa1-96a2-95c6de28f7a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_supported_positive_kernel_transform_gap

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ b : ℝ, 0 < b ∧
      ∀ s : ℝ, b ≤ s →
        (∫⁻ z : ℝ≥0, ENNReal.ofReal
          ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
          ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) <
          ENNReal.ofReal X.drift := by
  obtain ⟨κ, hκsf, hκsupp, hκLap, ⟨b, hb, hgap⟩⟩ :=
    bv_supported_positive_kernel_transform_gap X hX hbv q hq
  letI : SFinite κ := hκsf
  have hκset : κ {x : ℝ | ¬ 0 ≤ x} = 0 := by
    have hs : {x : ℝ | ¬ 0 ≤ x} = Iio (0 : ℝ) := by
      ext x
      simp
    rw [hs]
    exact hκsupp
  have hx : ∀ᵐ x : ℝ ∂κ, 0 ≤ x := (ae_iff).2 hκset
  refine ⟨b, hb, ?_⟩
  intro s hs
  have hspos : 0 < s := lt_of_lt_of_le hb hs
  have hmono :
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) ≤
        ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-b * x)) ∂κ := by
    apply lintegral_mono_ae
    filter_upwards [hx] with x hx'
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using
      neg_le_neg (mul_le_mul_of_nonneg_right hs hx')
  calc
    (∫⁻ z : ℝ≥0, ENNReal.ofReal
      ((1 - Real.exp (-(s + q / X.drift) * (z : ℝ))) / s)
      ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) =
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-s * x)) ∂κ) :=
          (hκLap s hspos).symm
    _ ≤ (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-b * x)) ∂κ) := hmono
    _ < ENNReal.ofReal X.drift := hgap
