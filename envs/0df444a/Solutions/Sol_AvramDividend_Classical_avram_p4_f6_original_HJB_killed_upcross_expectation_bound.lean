-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_original_HJB_killed_upcross_expectation_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:42:16.800184+00:00
-- url     : https://prove2.me/submissions/b6adad34-30b1-4471-88e7-c634c018edc9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_positive_deriv_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_finite_clock_budget_to_full
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_finite_original_upcross_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    ∀ b : ℝ, 1 ≤ b →
      w b * (twoSidedExitExpectationCorrected X q b 1).toReal ≤ w 1 := by
  have hS : {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} = Ioi (0 : ℝ) := by
    ext y
    simp [hTop]
  have hdifferentiable : ∀ y : ℝ, 0 < y → DifferentiableAt ℝ w y := by
    intro y hy
    have hmem : {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∈ 𝓝 y := by
      rw [hS]
      exact isOpen_Ioi.mem_nhds hy
    exact (hw_smooth.contDiffAt hmem).differentiableAt (by norm_num)
  have hgradient : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y := by
    intro y hy
    exact hw_grad y hy (by simp [hTop])
  have hnonnegative :=
    (avram_p4_f6_hjb_positive_deriv_monotone
      w hw0 hw_cont hdifferentiable hgradient).2
  intro b hb
  have hclocks := chat03_both_named_passage_clocks_measurable X (-1) (b - 1)
  have hu : Measurable (fun ω : Ω => twoSidedExitUpTimeCorrected X (b - 1) ω) := by
    change Measurable (fun ω : Ω => twoSidedExitUpTime X (b - 1) ω)
    exact hclocks.1
  have hd : Measurable (fun ω : Ω => twoSidedExitDownTimeCorrected X (-1) ω) := by
    change Measurable (fun ω : Ω => twoSidedExitDownTime X (-1) ω)
    exact hclocks.2
  have hv : Measurable (fun ω : Ω =>
      ENNReal.ofReal (Real.exp (-(q * (twoSidedExitUpTimeCorrected X (b - 1) ω).toReal)))) := by
    exact ((Real.measurable_exp.comp
      ((measurable_const.mul hu.ennreal_toReal).neg))).ennreal_ofReal
  have hbudget :=
    avram_p4_f6_hjb_finite_clock_budget_to_full P
      (fun ω : Ω => twoSidedExitUpTimeCorrected X (b - 1) ω)
      (fun ω : Ω => twoSidedExitDownTimeCorrected X (-1) ω)
      (fun ω : Ω => ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTimeCorrected X (b - 1) ω).toReal))))
      hu hd hv (w b) (w 1)
      (hnonnegative b (le_trans (by norm_num : (0:ℝ) ≤ 1) hb))
      (hnonnegative 1 (by norm_num))
      (fun n => avram_p4_f6_hjb_finite_original_upcross_budget
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad hTop b n hb)
  change w b * (∫⁻ ω,
    if twoSidedExitUpTimeCorrected X (b - 1) ω <
       twoSidedExitDownTimeCorrected X (-1) ω then
      ENNReal.ofReal
        (Real.exp (-(q * (twoSidedExitUpTimeCorrected X (b - 1) ω).toReal)))
    else 0 ∂P).toReal ≤ w 1
  exact hbudget
