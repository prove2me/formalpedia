-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f10_original_finite_stopped_discounted_payoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:01:55.963255+00:00
-- url     : https://prove2.me/submissions/875aefe2-bf41-4d40-8056-8ab43593229e

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_corrected_killed_discount_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The jointly measurable Lévy path can be evaluated at a measurable
corrected finite exit clock; a piecewise Borel HJB test remains measurable. -/
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
      Measurable (fun ω => Real.exp (-(q * ENNReal.toReal (τ ω))) *
        w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) := by
  classical
  intro b n hb
  let τ : Ω → ℝ≥0∞ := fun ω =>
    min (twoSidedExitUpTimeCorrected X (b - 1) ω)
      (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
  obtain ⟨hu, hd, _⟩ :=
    avram_p4_f6_hjb_corrected_killed_discount_measurable X q (-1) (b - 1)
  have hτ : Measurable τ :=
    hu.min (hd.min measurable_const)
  have hNN : Measurable (fun ω => ENNReal.toNNReal (τ ω)) :=
    ENNReal.measurable_toNNReal.comp hτ
  have hXEval : Measurable (fun ω => X.X (ENNReal.toNNReal (τ ω)) ω) := by
    simpa only [Function.comp_def, id_eq] using
      (chat04_levy_joint_time_state_measurable X).comp
        (hNN.prodMk measurable_id)
  have hp : Measurable ((Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ))) :=
    hw_cont.measurable_piecewise continuousOn_const measurableSet_Ici
  have hident : ((Ici (0 : ℝ)).piecewise w (fun _ => (0 : ℝ))) = w := by
    funext y
    by_cases hy : 0 ≤ y
    · simp [Set.piecewise, hy]
    · have hyneg : y < 0 := lt_of_not_ge hy
      simp [Set.piecewise, hy, hw_neg y hyneg]
  have hw : Measurable w := by simpa only [hident] using hp
  exact (Real.measurable_exp.comp
    ((measurable_const.mul hτ.ennreal_toReal).neg)).mul
    (hw.comp (measurable_const.add hXEval))
