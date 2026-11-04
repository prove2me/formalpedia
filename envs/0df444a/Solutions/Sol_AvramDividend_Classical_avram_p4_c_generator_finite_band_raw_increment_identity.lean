-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_finite_band_raw_increment_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:16:51.788433+00:00
-- url     : https://prove2.me/submissions/7379c56b-fdcb-432f-8aef-9b2bb393c63b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_cutoff_linear_mark_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hgen : X.GeneratorIntegrable w y) :
    (∫ z in Ioo (-1 : ℝ) (-ε), (w (y + z) - w y) ∂X.ν) =
      (∫ z in Ioo (-1 : ℝ) (-ε),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
      deriv w y * (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν) := by
  let S : Set ℝ := Ioo (-1 : ℝ) (-ε)
  have hsub : S ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact lt_trans hz.2 (neg_lt_zero.mpr hε)
  have hK : IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand w y)
      S X.ν := hgen.mono_set hsub
  have hz : IntegrableOn (fun z : ℝ => z) S X.ν :=
    avram_p4_c_generator_cutoff_linear_mark_integrable X ε hε
  have hlin : IntegrableOn (fun z : ℝ => deriv w y * z) S X.ν :=
    hz.const_mul (deriv w y)
  have hpoint : ∀ z ∈ S,
      w (y + z) - w y =
        SpectrallyNegativeLevy.generatorIntegrand w y z + deriv w y * z := by
    intro z hzS
    have hz0 : z < 0 := lt_trans hzS.2 (neg_lt_zero.mpr hε)
    have hmem : z ∈ Ioo (-1 : ℝ) 1 :=
      ⟨hzS.1, lt_trans hz0 (by norm_num)⟩
    simp [SpectrallyNegativeLevy.generatorIntegrand,
      Set.indicator_of_mem hmem]
  have hae : (fun z : ℝ => w (y + z) - w y) =ᵐ[X.ν.restrict S]
      (fun z => SpectrallyNegativeLevy.generatorIntegrand w y z + deriv w y * z) := by
    apply ae_restrict_of_forall_mem measurableSet_Ioo
    intro z hzS
    exact hpoint z hzS
  change (∫ z in S, w (y + z) - w y ∂X.ν) =
    (∫ z in S, SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
      deriv w y * (∫ z in S, z ∂X.ν)
  calc
    (∫ z in S, w (y + z) - w y ∂X.ν) =
        ∫ z in S, (SpectrallyNegativeLevy.generatorIntegrand w y z +
          deriv w y * z) ∂X.ν := integral_congr_ae hae
    _ = (∫ z in S, SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
        (∫ z in S, deriv w y * z ∂X.ν) := integral_add hK hlin
    _ = (∫ z in S, SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) +
        deriv w y * (∫ z in S, z ∂X.ν) := by rw [integral_const_mul]
