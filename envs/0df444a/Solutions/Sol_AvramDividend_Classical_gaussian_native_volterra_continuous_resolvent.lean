-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_native_volterra_continuous_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:15:45.095995+00:00
-- url     : https://prove2.me/submissions/0c17ff5a-a3bf-4a0d-928d-a422c2d0d152

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_native_double_tail_kernel_full_regularity
import Theorems.Thm_AvramDividend_Classical_gaussian_native_levy_esscher_double_tail_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_causal_volterra_l1_derivative_resolvent_exists
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Assemble the native monotone Gaussian kernel and its continuous Volterra resolvent. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    ∃ (a β : ℝ) (K g : ℝ → ℝ),
      0 < a ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      ContinuousOn K (Ioi (0 : ℝ)) ∧
      AntitoneOn K (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, 0 < t → 0 ≤ K t) ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      (∀ x : ℝ, 0 < x →
        a * V x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * V s ∂volume) = x) ∧
      (∀ x : ℝ, 0 < x →
        a * g x +
          (∫ s in Ioc (0 : ℝ) x,
            (β + K (x - s)) * g s ∂volume) = 1) := by
  let a : ℝ := X.σ ^ 2 / 2
  let β : ℝ :=
    X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
        ∂(X.ν.map (fun y : ℝ => -y)))
  let K : ℝ → ℝ := fun t : ℝ =>
    (∫⁻ z : ℝ,
      if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
      else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (pow_pos hσ 2) (by norm_num)
  have hKreg : Integrable K volume ∧
      ContinuousOn K (Ioi (0 : ℝ)) ∧
      AntitoneOn K (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, 0 < t → 0 ≤ K t) := by
    simpa only [K] using
      (gaussian_native_double_tail_kernel_full_regularity X φ hφ)
  rcases hKreg with ⟨_, hKcont, hKanti, hKpos⟩
  have hKint : IntegrableOn K (Ioi (0 : ℝ)) volume := by
    simpa only [K] using
      (gaussian_native_levy_esscher_double_tail_integrable X φ hφ)
  have hVEq : ∀ x : ℝ, 0 < x →
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume) = x := by
    exact gaussian_esscher_canonical_volterra_identity_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V hV a β K rfl rfl rfl
  obtain ⟨g, hg, hge⟩ :=
    causal_volterra_l1_derivative_resolvent_exists K a β ha hKint
  exact ⟨a, β, K, g, ha, hKint, hKcont, hKanti, hKpos, hg, hVEq, hge⟩