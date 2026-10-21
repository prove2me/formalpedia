-- Prove2me | solution 1 for AvramDividend.Classical.chat04_unbounded_closed_horizon_killed_scale_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T04:31:05.734819+00:00
-- url     : https://prove2.me/submissions/e735c42b-c771-45f0-95fb-0d8ec12e28d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_nat_pairing_rational_grid_coverage
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_survival_lintegral_grid_limit
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (x lower upper : ℝ) (T : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)}).indicator
          (fun ω => ENNReal.ofReal (W (x + X.X T ω))) ω ∂P) =
      ⨅ n : ℕ, ∫⁻ ω,
        ({ω | ∀ j ≤ n,
          (((Nat.unpair j).2 : ℝ≥0) * ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹) < T →
            ¬ (X.X (((Nat.unpair j).2 : ℝ≥0) * ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)) ω < lower ∨
               upper < X.X (((Nat.unpair j).2 : ℝ≥0) * ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)) ω)) ∧
          ¬ (X.X T ω < lower ∨ upper < X.X T ω)}).indicator
            (fun ω => ENNReal.ofReal (W (x + X.X T ω))) ω ∂P := by
  let τ : ℕ → ℝ≥0 := fun j => ((Nat.unpair j).2 : ℝ≥0) * ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹)
  let g : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (W (x + X.X T ω))
  have hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by
    intro n hn k
    simpa only [τ] using
      (AvramDividend.Classical.chat04_nat_pairing_rational_grid_coverage
        n k hn)
  have hWm : Measurable W :=
    AvramDividend.Classical.chat03_scale_function_borel_measurable
      X q W hW
  have hXt : Measurable (X.X T) :=
    (X.adapted T).mono (𝓕.le T) le_rfl
  have hFm : Measurable (fun ω : Ω => W (x + X.X T ω)) :=
    hWm.comp (measurable_const.add hXt)
  have hg : Measurable g :=
    ENNReal.measurable_ofReal.comp hFm
  have hNonneg : 0 ≤ᵐ[P] (fun ω => W (x + X.X T ω)) := by
    filter_upwards [] with ω
    by_cases hn : x + X.X T ω < 0
    · rw [hW.1 _ hn]
      exact le_rfl
    · exact hW.2.1 _ (le_of_not_gt hn)
  have hInt : Integrable (fun ω => W (x + X.X T ω)) P :=
    AvramDividend.Classical.chat04_unbounded_scale_fixed_time_integrable
      X q hq W hW hnbv x T
  have hFin : (∫⁻ ω, g ω ∂P) ≠ ∞ :=
    (lintegral_ofReal_ne_top_iff_integrable
      hFm.aestronglyMeasurable hNonneg).mpr hInt
  simpa only [τ, g] using
    (AvramDividend.Classical.chat04_closed_horizon_survival_lintegral_grid_limit
      X τ hCover lower upper T g hg hFin)
