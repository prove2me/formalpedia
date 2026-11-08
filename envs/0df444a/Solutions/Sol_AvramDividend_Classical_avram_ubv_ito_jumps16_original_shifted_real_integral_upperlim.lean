-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps16_original_shifted_real_integral_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:27:24.246942+00:00
-- url     : https://prove2.me/submissions/69ef73ee-2f78-45f7-a6f6-7f980e9648ec

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_shifted_lintegral_upperlim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Convert the accepted shifted Levy lintegral reverse-Fatou estimate to a
real Bochner-integral upper limit, keeping the genuine original process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ → ℝ) (hhmeas : Measurable h)
    (hh_nonneg : ∀ z : ℝ, 0 ≤ h z)
    (hhfinite : (∫⁻ z, ENNReal.ofReal (2 * h z) ∂X.ν) ≠ ⊤)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hfmeas : ∀ n, Measurable (f n)) (hgmeas : Measurable g)
    (habs : ∀ n z, |f n z| ≤ h z)
    (hgabs : ∀ z, |g z| ≤ h z)
    (hpoint : ∀ᵐ z ∂X.ν,
      Filter.limsup (fun n : ℕ => ENNReal.ofReal (h z + f n z)) atTop ≤
        ENNReal.ofReal (h z + g z)) :
    Filter.limsup
      (fun n : ℕ => ∫ z, h z + f n z ∂X.ν) atTop ≤
      ∫ z, h z + g z ∂X.ν := by
  let B : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (2 * h z) ∂X.ν
  have hbound (n : ℕ) :
      (∫⁻ z, ENNReal.ofReal (h z + f n z) ∂X.ν) ≤ B := by
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    have hn := (abs_le.mp (habs n z)).2
    linarith
  have hgbound :
      (∫⁻ z, ENNReal.ofReal (h z + g z) ∂X.ν) ≤ B := by
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    have hn := (abs_le.mp (hgabs z)).2
    linarith
  have hgfinite :
      (∫⁻ z, ENNReal.ofReal (h z + g z) ∂X.ν) ≠ ⊤ := by
    intro htop
    exact hhfinite (top_le_iff.mp (htop ▸ hgbound))
  have hreal (n : ℕ) :
      (∫ z, h z + f n z ∂X.ν) =
        (∫⁻ z, ENNReal.ofReal (h z + f n z) ∂X.ν).toReal := by
    apply MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall (fun z => by
        change 0 ≤ h z + f n z
        have hn := (abs_le.mp (habs n z)).1
        linarith)
    · exact (hhmeas.add (hfmeas n)).aestronglyMeasurable
  have hgreal :
      (∫ z, h z + g z ∂X.ν) =
        (∫⁻ z, ENNReal.ofReal (h z + g z) ∂X.ν).toReal := by
    apply MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall (fun z => by
        change 0 ≤ h z + g z
        have hn := (abs_le.mp (hgabs z)).1
        linarith)
    · exact (hhmeas.add hgmeas).aestronglyMeasurable
  have hlim :=
    avram_ubv_ito_jumps16_original_shifted_lintegral_upperlim
      X h hhmeas hh_nonneg hhfinite f g hfmeas habs hpoint
  calc
    Filter.limsup (fun n : ℕ => ∫ z, h z + f n z ∂X.ν) atTop =
        Filter.limsup
          (fun n : ℕ => (∫⁻ z, ENNReal.ofReal (h z + f n z) ∂X.ν).toReal) atTop := by
          congr 1
          funext n
          exact hreal n
    _ = (Filter.limsup
          (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (h z + f n z) ∂X.ν) atTop).toReal :=
        (ENNReal.limsup_toReal_eq hhfinite
          (Filter.Eventually.of_forall hbound))
    _ ≤ (∫⁻ z, ENNReal.ofReal (h z + g z) ∂X.ν).toReal :=
      ENNReal.toReal_mono hgfinite hlim
    _ = ∫ z, h z + g z ∂X.ν := hgreal.symm
