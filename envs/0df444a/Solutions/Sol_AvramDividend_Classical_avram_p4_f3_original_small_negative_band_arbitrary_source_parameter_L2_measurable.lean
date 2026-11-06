-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:27:21.229022+00:00
-- url     : https://prove2.me/submissions/177d8821-1675-4e2a-93d3-0296e99cf8f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_full_levy_sfinite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original negative-band intensity is measurable in an arbitrary measurable source parameter, including physical time-reserve pairs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {S : Type*} [mS : MeasurableSpace S]
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (U V : S → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (ε : ℝ) :
    Measurable (fun s =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U s + z) - w (U s)) -
            (w (V s + z) - w (V s))) ^ 2) ∂X.ν)) := by
  let B : Set ℝ := Ioo (-ε) (0 : ℝ)
  let f : S → ℝ → ℝ≥0∞ := fun s z =>
    B.indicator (fun z =>
      ENNReal.ofReal
        (((w (U s + z) - w (U s)) -
          (w (V s + z) - w (V s))) ^ 2)) z
  have hwMeas : Measurable w :=
    avram_p4_c_generator_zero_negative_payoff_measurable w hw_cont hw_neg
  have hUfst : Measurable (fun p : S × ℝ => U p.1) :=
    hU.comp measurable_fst
  have hVfst : Measurable (fun p : S × ℝ => V p.1) :=
    hV.comp measurable_fst
  have h1 : Measurable (fun p : S × ℝ => w (U p.1 + p.2)) :=
    hwMeas.comp (hUfst.add measurable_snd)
  have h2 : Measurable (fun p : S × ℝ => w (V p.1 + p.2)) :=
    hwMeas.comp (hVfst.add measurable_snd)
  have h3 : Measurable (fun p : S × ℝ => w (U p.1)) :=
    hwMeas.comp hUfst
  have h4 : Measurable (fun p : S × ℝ => w (V p.1)) :=
    hwMeas.comp hVfst
  have hRaw : Measurable (fun p : S × ℝ =>
      ENNReal.ofReal
        (((w (U p.1 + p.2) - w (U p.1)) -
          (w (V p.1 + p.2) - w (V p.1))) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((h1.sub h3).sub (h2.sub h4)).pow_const 2)
  have hf : Measurable (Function.uncurry f) := by
    exact hRaw.indicator (measurableSet_Ioo.preimage measurable_snd)
  letI : SFinite X.ν :=
    avram_p2_e_compensator_original_full_levy_sfinite X
  have hMeas : Measurable (fun s => ∫⁻ z, f s z ∂X.ν) :=
    Measurable.lintegral_prod_right hf
  have hEq :
      (fun s => ∫⁻ z, f s z ∂X.ν) =
      (fun s =>
        (∫⁻ z in Ioo (-ε) (0 : ℝ),
          ENNReal.ofReal
            (((w (U s + z) - w (U s)) -
              (w (V s + z) - w (V s))) ^ 2) ∂X.ν)) := by
    funext s
    dsimp [f, B]
    rw [lintegral_indicator measurableSet_Ioo]
  rw [← hEq]
  exact hMeas
