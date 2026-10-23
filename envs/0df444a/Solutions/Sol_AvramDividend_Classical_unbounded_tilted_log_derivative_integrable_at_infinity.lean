-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_tilted_log_derivative_integrable_at_infinity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:55:32.345253+00:00
-- url     : https://prove2.me/submissions/0263cbe9-eac6-4ec6-91c9-1d56481548b3

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_log_derivative_nonintegrable_at_origin
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (hVdiff : ∀ x : ℝ, 0 < x → HasDerivAt V (deriv V x) x) :
    ∃ (μ : Measure ℝ),
      (∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x →
        μ.real (Ici x) = ∫ y in Ioi (0 : ℝ), (deriv V y / V y) ∂volume) := by
  have hnot : ¬ IntegrableOn
      (fun y : ℝ => deriv V y / V y) (Ioi (0 : ℝ)) :=
    unbounded_tilted_log_derivative_nonintegrable_at_origin
      X q hq W hW hnbv φ hφ hroot V hV hVdiff
  have hzero :
      (∫ y in Ioi (0 : ℝ), (deriv V y / V y) ∂volume) = 0 := by
    exact integral_undef hnot
  refine ⟨0, ?_, ?_⟩
  · intro x hx
    simp
  · intro x hx
    simp [hzero]
