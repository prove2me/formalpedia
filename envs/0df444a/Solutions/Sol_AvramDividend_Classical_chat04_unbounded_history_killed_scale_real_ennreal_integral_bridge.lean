-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_history_killed_scale_real_ennreal_integral_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T18:12:24.611321+00:00
-- url     : https://prove2.me/submissions/d3299e89-fab4-488a-9d42-eaf1a011c946

import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Convert the full-history killed real scale expectation without a growth witness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
    ENNReal.ofReal (∫ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)) ω ∂P) := by
  let S : Set Ω := {u | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}
  let f : Ω → ℝ := fun u =>
    Real.exp (-(q * (t : ℝ))) * W (x + X.X t u)
  have hRaw : Integrable (fun u : Ω => W (x + X.X t u)) P :=
    chat04_unbounded_scale_fixed_time_integrable X q hq W hW hnbv x t
  have hDisc : Integrable f P := by
    dsimp [f]
    exact hRaw.const_mul _
  have hS : MeasurableSet S := by
    dsimp [S]
    exact chat04_shifted_lower_survival_measurable_no_schedule X x t
  have hKilled : Integrable (S.indicator f) P := hDisc.indicator hS
  have hNonneg : ∀ u, 0 ≤ S.indicator f u := by
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      exact mul_nonneg (Real.exp_nonneg _) (hW.2.1 _ (hu t le_rfl))
    · rw [Set.indicator_of_notMem hu]
  change (∫⁻ u, S.indicator (fun v => ENNReal.ofReal (f v)) u ∂P) =
    ENNReal.ofReal (∫ u, S.indicator f u ∂P)
  calc
    (∫⁻ u, S.indicator (fun v => ENNReal.ofReal (f v)) u ∂P) =
        (∫⁻ u, ENNReal.ofReal (S.indicator f u) ∂P) := by
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ S
      · simp only [Set.indicator_of_mem hu]
      · simp only [Set.indicator_of_notMem hu, ENNReal.ofReal_zero]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal hKilled
      (Filter.Eventually.of_forall hNonneg)).symm
