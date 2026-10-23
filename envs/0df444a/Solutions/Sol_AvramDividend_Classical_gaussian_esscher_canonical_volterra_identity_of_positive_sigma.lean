-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_canonical_volterra_identity_of_positive_sigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:19:39.452968+00:00
-- url     : https://prove2.me/submissions/9f454f86-0d40-433c-bb9a-024abf3b8c91

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_residual_continuous_on_positive
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_residual_laplace_eq_linear
import Theorems.Thm_AvramDividend_Classical_continuousOn_Ioi_eq_of_laplace_eq_signed
import Theorems.Thm_AvramDividend_Classical_positive_laplace_linear_reference
import Theorems.Thm_AvramDividend_Classical_positive_laplace_linear_reference_integrable

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
      V x = Real.exp (-(φ * x)) * W x)
    (a β : ℝ) (K : ℝ → ℝ)
    (ha : a = X.σ ^ 2 / 2)
    (hβ : β =
      X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
        X.σ ^ 2 * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
          ∂(X.ν.map (fun y : ℝ => -y))))
    (hK : K = fun t : ℝ =>
      (∫⁻ z : ℝ,
        if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
        else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal) :
    ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x := by
  let F : ℝ → ℝ := fun x =>
    a * V x + ∫ s in Ioc (0 : ℝ) x,
      (β + K (x - s)) * V s ∂volume
  have hFc : ContinuousOn F (Ioi (0 : ℝ)) :=
    gaussian_esscher_volterra_residual_continuous_on_positive
      X q hq W hW hσ φ hφ hroot V hV a β K ha hβ hK
  have hIdc : ContinuousOn (fun x : ℝ => x) (Ioi (0 : ℝ)) :=
    continuous_id.continuousOn
  apply continuousOn_Ioi_eq_of_laplace_eq_signed F (fun x : ℝ => x) 0
    hFc hIdc
  intro θ hθ
  obtain ⟨hFi, hFl⟩ :=
    gaussian_esscher_volterra_residual_laplace_eq_linear
      X q hq W hW hσ φ hφ hroot V hV a β K ha hβ hK θ hθ
  refine ⟨?_, ?_, ?_⟩
  · simpa only [F, neg_mul] using hFi
  · simpa only [neg_mul] using
      (positive_laplace_linear_reference_integrable θ hθ)
  · have hFl' :
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * F x ∂volume) =
          (1 / θ) ^ 2 := by
        simpa only [F, neg_mul] using hFl
    have hId' :
        (∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) * x ∂volume) =
          (1 / θ) ^ 2 := by
        simpa only [neg_mul] using
          (positive_laplace_linear_reference θ hθ)
    exact hFl'.trans hId'.symm
