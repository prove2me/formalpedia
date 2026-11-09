-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_nu_smallstrip_lintegral_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:33:17.769822+00:00
-- url     : https://prove2.me/submissions/9bfbc2a0-791c-4b7e-8bc4-5167b3fddaa7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- Finite negative-jump intensity bounds the deterministic compensated
first moment on a shrinking strip of the original Lévy measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (ε : ℝ) (hε : 0 ≤ ε) :
    (∫⁻ z in Ioo (-ε) 0, ENNReal.ofReal |z| ∂X.ν) ≤
      ENNReal.ofReal ε * X.ν (Iio (0 : ℝ)) := by
  classical
  let S : Set ℝ := Ioo (-ε) 0
  have hS : MeasurableSet S := measurableSet_Ioo
  have hsubset : S ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact hz.2
  have hAe : ∀ᵐ z ∂X.ν.restrict S,
      ENNReal.ofReal |z| ≤ ENNReal.ofReal ε := by
    filter_upwards [ae_restrict_mem hS] with z hz
    apply ENNReal.ofReal_le_ofReal
    have hneg : |z| = -z := abs_of_neg hz.2
    rw [hneg]
    linarith [hz.1]
  have hmass : X.ν S ≤ X.ν (Iio (0 : ℝ)) := measure_mono hsubset
  calc
    (∫⁻ z in Ioo (-ε) 0, ENNReal.ofReal |z| ∂X.ν) =
        ∫⁻ z, ENNReal.ofReal |z| ∂X.ν.restrict S := by rfl
    _ ≤ ∫⁻ _z, ENNReal.ofReal ε ∂X.ν.restrict S :=
      lintegral_mono_ae hAe
    _ = ENNReal.ofReal ε * X.ν S := by
      rw [lintegral_const]
      simp [S, hS]
    _ ≤ ENNReal.ofReal ε * X.ν (Iio (0 : ℝ)) :=
      mul_le_mul_of_nonneg_left hmass zero_le
