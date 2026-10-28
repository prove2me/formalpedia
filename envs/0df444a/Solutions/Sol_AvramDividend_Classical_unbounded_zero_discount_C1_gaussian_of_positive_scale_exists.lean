-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_zero_discount_C1_gaussian_of_positive_scale_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:41:21.216952+00:00
-- url     : https://prove2.me/submissions/c77a2389-c923-4469-8a10-7bb67d06af33

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_unbounded_zero_discount_C1_of_positive_discount_C1
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A positive Gaussian part reduces q=0 scale C1 to positive-q scale existence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hσ : 0 < X.σ)
    (hexists : ∃ q : ℝ, 0 < q ∧
      ∃ Wq : ℝ → ℝ, IsScaleFunction X q Wq) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) := by
  obtain ⟨q, hq, Wq, hWq⟩ := hexists
  obtain ⟨β, hβ, hψ⟩ :=
    chat04_psi_eventually_gt_of_unbounded_variation X q hq hnbv
  have hC1 : ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) :=
    scaleFunction_contDiff_one_gaussian_without_standing
      X q hq Wq hWq hσ
  exact unbounded_zero_discount_C1_of_positive_discount_C1
    X hnbv W₀ hW₀ q hq Wq hWq hC1 β hβ (hψ β le_rfl)
