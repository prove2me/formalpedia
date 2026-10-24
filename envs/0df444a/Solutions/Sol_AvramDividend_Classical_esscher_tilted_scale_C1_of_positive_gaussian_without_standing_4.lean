-- Prove2me | solution 4 for AvramDividend.Classical.esscher_tilted_scale_C1_of_positive_gaussian_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:39:03.004994+00:00
-- url     : https://prove2.me/submissions/c96bf090-dd77-4f79-93e3-b9c3322406e7

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_kernel_equation_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_tilted_scale_locally_bounded
import Theorems.Thm_AvramDividend_Classical_integrated_volterra_regularizes_C1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x) :
    ContDiffOn ℝ 1 V (Ioi (0 : ℝ)) := by
  obtain ⟨a, β, K, ha, hK, hEq⟩ :=
    gaussian_esscher_volterra_kernel_equation_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V hV
  have hVcont : ContinuousOn V (Ioi (0 : ℝ)) :=
    gaussian_esscher_tilted_scale_continuous
      X q hq W hW hσ φ V hV
  have hVbound : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |V x| ≤ C :=
    gaussian_esscher_tilted_scale_locally_bounded
      X q hq W hW hσ φ hφ V hV
  exact integrated_volterra_regularizes_C1 V K a β
    ha hK hVcont hVbound hEq
