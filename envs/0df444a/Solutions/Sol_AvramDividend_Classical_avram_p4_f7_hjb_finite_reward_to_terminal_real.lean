-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f7_hjb_finite_reward_to_terminal_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:27:16.358878+00:00
-- url     : https://prove2.me/submissions/15c4ecc7-0448-4c98-9783-438fc4e4a16f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_avram_p4_f7_hjb_topcap_global_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_hjb_finite_reward_pathwise_le_terminal
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_hjb_finite_terminal_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_f8_generic_bounded_lintegral_real_transfer

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Combine the physical stopped-clock comparison with a bounded probability lintegral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 ≤ b →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      w b * (∫⁻ ω,
        if twoSidedExitUpTimeCorrected X (b - 1) ω <
             twoSidedExitDownTimeCorrected X (-1) ω ∧
           twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞) then
          ENNReal.ofReal (Real.exp (-(q *
            ENNReal.toReal (twoSidedExitUpTimeCorrected X (b - 1) ω))))
        else 0 ∂P).toReal ≤
      (∫⁻ ω, ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (τ ω))) *
          w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) ∂P).toReal := by
  intro b n hb
  let τ : Ω → ℝ≥0∞ := fun ω =>
    min (twoSidedExitUpTimeCorrected X (b - 1) ω)
      (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
  let f : Ω → ℝ≥0∞ := fun ω =>
    if twoSidedExitUpTimeCorrected X (b - 1) ω <
         twoSidedExitDownTimeCorrected X (-1) ω ∧
       twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞) then
      ENNReal.ofReal (Real.exp (-(q *
        ENNReal.toReal (twoSidedExitUpTimeCorrected X (b - 1) ω))))
    else 0
  let g : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (τ ω))) *
      w (1 + X.X (ENNReal.toNNReal (τ ω)) ω))
  change w b * (∫⁻ ω, f ω ∂P).toReal ≤ (∫⁻ ω, g ω ∂P).toReal
  letI : IsProbabilityMeasure P := X.isProbability
  have hn := avram_p4_f7_hjb_topcap_global_nonnegative
    w C hw0 hw_cont hw_neg hw_smooth hw_grad hTop
  have hwb : 0 ≤ w b := hn b
  have hf : ∀ ω, f ω ≤ 1 := by
    intro ω
    dsimp [f]
    split_ifs with he
    · have hx : 0 ≤ q * ENNReal.toReal
        (twoSidedExitUpTimeCorrected X (b - 1) ω) :=
        mul_nonneg hq.le ENNReal.toReal_nonneg
      have hh : Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTimeCorrected X (b - 1) ω))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        linarith
      exact (ENNReal.ofReal_le_ofReal hh).trans (by norm_num)
    · norm_num
  have hg : ∀ ω, g ω ≤ ENNReal.ofReal (w b) := by
    intro ω
    exact avram_p4_f8_hjb_finite_terminal_envelope
      X hX w C hw0 hw_cont hw_neg hw_smooth hw_grad hTop q hq b n hb ω
  have hfg : ∀ ω, ENNReal.ofReal (w b) * f ω ≤ g ω := by
    intro ω
    have hpoint := avram_p4_f8_hjb_finite_reward_pathwise_le_terminal
      X hX w C hw0 hw_cont hw_neg hw_smooth hw_grad hTop q hq b n hb ω
    by_cases he :
      twoSidedExitUpTimeCorrected X (b - 1) ω <
        twoSidedExitDownTimeCorrected X (-1) ω ∧
      twoSidedExitUpTimeCorrected X (b - 1) ω ≤ (n : ℝ≥0∞)
    · dsimp [f]
      rw [if_pos he]
      have hm : ENNReal.ofReal (w b) *
          ENNReal.ofReal (Real.exp (-(q *
            ENNReal.toReal (twoSidedExitUpTimeCorrected X (b - 1) ω)))) =
          ENNReal.ofReal (Real.exp (-(q *
            ENNReal.toReal (twoSidedExitUpTimeCorrected X (b - 1) ω))) * w b) := by
        rw [← ENNReal.ofReal_mul hwb, mul_comm]
      rw [hm]
      simpa only [if_pos he, g, τ] using hpoint
    · simp [f, he]
  exact avram_p4_f8_generic_bounded_lintegral_real_transfer
    P (w b) hwb f g hf hg hfg
