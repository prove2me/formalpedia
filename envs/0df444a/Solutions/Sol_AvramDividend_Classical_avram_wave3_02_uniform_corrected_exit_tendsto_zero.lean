-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_corrected_exit_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T22:03:37.957811+00:00
-- url     : https://prove2.me/submissions/00378ffb-f426-4e89-a310-7b60d59213bd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_corrected_exit_exp_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- True discounted upper exits before ruin vanish uniformly in every
bounded interval of nonnegative initial reserves at an infinite barrier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun a : ℝ =>
      ⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        twoSidedExitExpectationCorrected X q a x)
      atTop (𝓝 (0 : ENNReal)) := by
  obtain ⟨φ, hφ, hbound⟩ :=
    avram_wave3_02_uniform_corrected_exit_exp_bound X hX q hq W hW
  have hlin : Tendsto (fun a : ℝ => a * (-φ)) atTop atBot :=
    Filter.Tendsto.atTop_mul_const_of_neg (by linarith : -φ < 0) tendsto_id
  have hshift : Tendsto (fun a : ℝ => a * (-φ) + φ * (R + 1)) atTop atBot :=
    Filter.tendsto_atBot_add_const_right atTop (φ * (R + 1)) hlin
  have hexp : Tendsto (fun a : ℝ => Real.exp (-φ * (a - (R + 1))))
      atTop (𝓝 (0 : ℝ)) := by
    have heq : (fun a : ℝ => Real.exp (-φ * (a - (R + 1)))) =
        (fun a : ℝ => Real.exp (a * (-φ) + φ * (R + 1))) := by
      funext a
      congr 1
      ring
    rw [heq]
    exact Real.tendsto_exp_atBot.comp hshift
  have hupper : Tendsto (fun a : ℝ =>
      ENNReal.ofReal (Real.exp (-φ * (a - (R + 1)))))
      atTop (𝓝 (0 : ENNReal)) := by
    have ht := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hexp
    change Tendsto (fun a : ℝ =>
      ENNReal.ofReal (Real.exp (-φ * (a - (R + 1)))))
      atTop (𝓝 (ENNReal.ofReal (0 : ℝ))) at ht
    simpa only [ENNReal.ofReal_zero] using ht
  have hevent : ∀ᶠ a : ℝ in atTop,
      (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
        twoSidedExitExpectationCorrected X q a x) ≤
      ENNReal.ofReal (Real.exp (-φ * (a - (R + 1)))) := by
    filter_upwards [eventually_ge_atTop (R + 1)] with a ha
    exact hbound R a hR ha
  exact Filter.Tendsto.squeeze'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ENNReal)) atTop (𝓝 0))
    hupper (Filter.Eventually.of_forall
      (fun a => (show (0 : ENNReal) ≤
        (⨆ x : ℝ, ⨆ (_ : 0 ≤ x ∧ x ≤ R),
          twoSidedExitExpectationCorrected X q a x) from zero_le))) hevent
