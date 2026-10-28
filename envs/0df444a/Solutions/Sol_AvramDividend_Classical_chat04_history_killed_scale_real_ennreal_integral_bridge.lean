-- Prove2me | solution 1 for AvramDividend.Classical.chat04_history_killed_scale_real_ennreal_integral_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T15:22:18.628728+00:00
-- url     : https://prove2.me/submissions/39bcbd8f-104e-42aa-94e7-3ec1aa59435c

import Theorems.Thm_AvramDividend_Classical_chat04_killed_deterministic_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
/-- The L² moment estimate converts the history-killed real expectation into
its extended-nonnegative integral, with no external grid schedule. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
    ENNReal.ofReal (∫ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω ∂P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let S : Set Ω := {u | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}
  let Y : Ω → ℝ := S.indicator (fun u =>
    Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))
  have hS : MeasurableSet S :=
    chat04_shifted_lower_survival_measurable_no_schedule X x t
  have hR : Measurable (X.X t) :=
    (X.adapted t).mono (𝓕.le t) le_rfl
  have hScale : Measurable (fun u => W (x + X.X t u)) :=
    (chat03_scale_function_borel_measurable X q W hW).comp
      (measurable_const.add hR)
  have hDisc : Measurable (fun _ : Ω => Real.exp (-(q * (t : ℝ)))) := measurable_const
  have hProd : Measurable (fun u : Ω => Real.exp (-(q * (t : ℝ))) *
      W (x + X.X t u)) := by
    convert (hDisc.mul hScale) using 1
    funext u
    simp only [Pi.mul_apply]
  have hYm : AEStronglyMeasurable Y P :=
    (hProd.indicator hS).aestronglyMeasurable
  have hY0 : ∀ u, 0 ≤ Y u := by
    intro u
    by_cases hm : u ∈ S
    · rw [show Y u =
        Real.exp (-(q * (t : ℝ))) * W (x + X.X t u) from
          Set.indicator_of_mem hm _]
      apply mul_nonneg (Real.exp_nonneg _)
      by_cases hy : 0 ≤ x + X.X t u
      · exact hW.2.1 _ hy
      · simp [hW.1 _ (lt_of_not_ge hy)]
    · simp [Y, Set.indicator_of_notMem hm]
  have hY2 : Integrable (fun u => (Y u)^2) P := by
    have h := chat04_killed_deterministic_horizon_scale_l2_bound
      X q hq W hW θ x hθ hψ t t le_rfl S hS
    simpa [Y] using h.1
  have hUpper : ∀ u, Y u ≤ 1 + (Y u)^2 := by
    intro u
    nlinarith [sq_nonneg (Y u - (1 / 2 : ℝ))]
  have hY : Integrable Y P :=
    integrable_of_le_of_le hYm
      (Filter.Eventually.of_forall hY0)
      (Filter.Eventually.of_forall hUpper)
      (integrable_const (0 : ℝ))
      ((integrable_const (1 : ℝ)).add hY2)
  change (∫⁻ u, S.indicator (fun v => ENNReal.ofReal
    (Real.exp (-(q * (t : ℝ))) * W (x + X.X t v))) u ∂P) =
      ENNReal.ofReal (∫ u, Y u ∂P)
  calc
    (∫⁻ u, S.indicator (fun v => ENNReal.ofReal
      (Real.exp (-(q * (t : ℝ))) * W (x + X.X t v))) u ∂P) =
        (∫⁻ u, ENNReal.ofReal (Y u) ∂P) := by
          congr 1
          funext u
          by_cases hu : u ∈ S
          · simp [Y, Set.indicator_of_mem hu]
          · simp [Y, Set.indicator_of_notMem hu]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal hY
      (Filter.Eventually.of_forall hY0)).symm