-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_small_negative_band_random_reserve_coefficient_L2_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:14:56.557391+00:00
-- url     : https://prove2.me/submissions/bbf235cd-109e-4b71-80eb-06a79905a2c6

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

/-- Original negative-jump intensity is a measurable function of the random reserve states. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (U V : Ω → ℝ)
    (hU : Measurable U) (hV : Measurable V)
    (ε : ℝ) :
    Measurable (fun ω =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U ω + z) - w (U ω)) -
            (w (V ω + z) - w (V ω))) ^ 2) ∂X.ν)) := by
  let B : Set ℝ := Ioo (-ε) (0 : ℝ)
  let f : Ω → ℝ → ℝ≥0∞ := fun ω z =>
    B.indicator (fun z =>
      ENNReal.ofReal
        (((w (U ω + z) - w (U ω)) -
          (w (V ω + z) - w (V ω))) ^ 2)) z
  have hwMeas : Measurable w :=
    avram_p4_c_generator_zero_negative_payoff_measurable w hw_cont hw_neg
  have hUfst : Measurable (fun p : Ω × ℝ => U p.1) :=
    hU.comp measurable_fst
  have hVfst : Measurable (fun p : Ω × ℝ => V p.1) :=
    hV.comp measurable_fst
  have h1 : Measurable (fun p : Ω × ℝ => w (U p.1 + p.2)) :=
    hwMeas.comp (hUfst.add measurable_snd)
  have h2 : Measurable (fun p : Ω × ℝ => w (V p.1 + p.2)) :=
    hwMeas.comp (hVfst.add measurable_snd)
  have h3 : Measurable (fun p : Ω × ℝ => w (U p.1)) :=
    hwMeas.comp hUfst
  have h4 : Measurable (fun p : Ω × ℝ => w (V p.1)) :=
    hwMeas.comp hVfst
  have hRaw : Measurable (fun p : Ω × ℝ =>
      ENNReal.ofReal
        (((w (U p.1 + p.2) - w (U p.1)) -
          (w (V p.1 + p.2) - w (V p.1))) ^ 2)) :=
    ENNReal.measurable_ofReal.comp
      (((h1.sub h3).sub (h2.sub h4)).pow_const 2)
  have hf : Measurable (Function.uncurry f) := by
    exact hRaw.indicator (measurableSet_Ioo.preimage measurable_snd)
  letI : SFinite X.ν :=
    avram_p2_e_compensator_original_full_levy_sfinite X
  have hMeas : Measurable (fun ω => ∫⁻ z, f ω z ∂X.ν) :=
    Measurable.lintegral_prod_right hf
  have hEq :
      (fun ω => ∫⁻ z, f ω z ∂X.ν) =
      (fun ω =>
        (∫⁻ z in Ioo (-ε) (0 : ℝ),
          ENNReal.ofReal
            (((w (U ω + z) - w (U ω)) -
              (w (V ω + z) - w (V ω))) ^ 2) ∂X.ν)) := by
    funext ω
    dsimp [f, B]
    rw [lintegral_indicator measurableSet_Ioo]
  rw [← hEq]
  exact hMeas
