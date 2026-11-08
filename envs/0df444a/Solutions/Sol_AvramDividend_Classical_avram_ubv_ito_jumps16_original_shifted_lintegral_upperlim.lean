-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps16_original_shifted_lintegral_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:00:05.662525+00:00
-- url     : https://prove2.me/submissions/595e7413-1ec9-4bbd-a05b-f63488836d57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Domination turns a pointwise one-sided shifted upper limit into an
integrated one for the genuine negative jump measure of the given Lévy law.
This is the nonnegative lintegral stage of signed reverse Fatou. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ → ℝ) (hhmeas : Measurable h)
    (hh_nonneg : ∀ z : ℝ, 0 ≤ h z)
    (hhfinite : (∫⁻ z, ENNReal.ofReal (2 * h z) ∂X.ν) ≠ ⊤)
    (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hfmeas : ∀ n, Measurable (f n))
    (habs : ∀ n z, |f n z| ≤ h z)
    (hpoint : ∀ᵐ z ∂X.ν,
      Filter.limsup (fun n : ℕ => ENNReal.ofReal (h z + f n z)) atTop ≤
        ENNReal.ofReal (h z + g z)) :
    Filter.limsup
      (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (h z + f n z) ∂X.ν) atTop ≤
      ∫⁻ z, ENNReal.ofReal (h z + g z) ∂X.ν := by
  have hm (n : ℕ) :
      Measurable (fun z : ℝ => ENNReal.ofReal (h z + f n z)) :=
    ENNReal.measurable_ofReal.comp (hhmeas.add (hfmeas n))
  have hd (n : ℕ) :
      (fun z : ℝ => ENNReal.ofReal (h z + f n z)) ≤ᵐ[X.ν]
        (fun z : ℝ => ENNReal.ofReal (2 * h z)) := by
    apply Filter.Eventually.of_forall
    intro z
    apply ENNReal.ofReal_le_ofReal
    have hf := (abs_le.mp (habs n z)).2
    linarith
  calc
    Filter.limsup
        (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (h z + f n z) ∂X.ν) atTop
        ≤ ∫⁻ z, Filter.limsup
          (fun n : ℕ => ENNReal.ofReal (h z + f n z)) atTop ∂X.ν :=
          MeasureTheory.limsup_lintegral_le
            (fun z : ℝ => ENNReal.ofReal (2 * h z)) hm hd hhfinite
    _ ≤ ∫⁻ z, ENNReal.ofReal (h z + g z) ∂X.ν :=
      lintegral_mono_ae hpoint
