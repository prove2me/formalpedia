-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_volterra_C1_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:59:21.905325+00:00
-- url     : https://prove2.me/submissions/5a3b76c3-4d4f-4ed4-a7a0-69c0579626ee

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_kernel_equation_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_integrated_volterra_regularizes_C1
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_continuous_solution_unique
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) ∧
    ∃ (a β : ℝ) (K : ℝ → ℝ),
      0 < a ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      (∀ x : ℝ, 0 < x →
        a * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x) ∧
      (∀ G : ℝ → ℝ,
        ContinuousOn G (Ioi (0 : ℝ)) →
        (∀ R : ℝ, 0 < R →
          ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) →
        (∀ x : ℝ, 0 < x →
          a * G x +
            (∫ s in Ioc (0 : ℝ) x,
              (β + K (x - s)) * G s ∂volume) = x) →
        ∀ x : ℝ, 0 < x → G x = V x) := by
  have hVc : ContinuousOn V (Ioi (0 : ℝ)) :=
    gaussian_esscher_tilted_scale_continuous X q hq W hW hσ φ V hV
  have hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C :=
    gaussian_esscher_tilted_scale_locally_bounded X q hq W hW hσ φ hφ V hV
  obtain ⟨a, β, K, ha, hKi, hEq⟩ :=
    gaussian_esscher_volterra_kernel_equation_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V hV
  have hVdiff : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) :=
    integrated_volterra_regularizes_C1 V K a β ha hKi hVc hVb hEq
  refine ⟨hVdiff, a, β, K, ha, hKi, hEq, ?_⟩
  intro G hGc hGb hGe x hx
  exact causal_volterra_l1_continuous_solution_unique
    K a β ha hKi G V hGc hVc hGb hVb hGe hEq x hx
