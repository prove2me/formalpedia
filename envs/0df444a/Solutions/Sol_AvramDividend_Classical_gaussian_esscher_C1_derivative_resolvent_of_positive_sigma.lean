-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_C1_derivative_resolvent_of_positive_sigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T06:56:57.420184+00:00
-- url     : https://prove2.me/submissions/9497e406-06d9-43d0-a3fb-52660167d22b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_native_double_tail_kernel_full_regularity
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_canonical_volterra_identity_of_positive_sigma
import Theorems.Thm_AvramDividend_Classical_causal_gaussian_C1_volterra_resolvent_from_antitone_kernel
import Mathlib.Analysis.Complex.Exponential

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
    ∃ (a β : ℝ) (K g : ℝ → ℝ),
      0 < a ∧
      IntegrableOn K (Ioi (0 : ℝ)) volume ∧
      ContinuousOn g (Ici (0 : ℝ)) ∧
      ContDiffOn ℝ 1 g (Ioi (0 : ℝ)) ∧
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
    positivity
  obtain ⟨hKI, hKC, hKA, hKP⟩ :=
    gaussian_native_double_tail_kernel_full_regularity X φ hφ
  have hKpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ K t := by
    intro t ht
    rcases eq_or_lt_of_le ht with hzero | hpositive
    · subst t
      simp [K]
    · exact hKP t hpositive
  have hVeq :=
    gaussian_esscher_canonical_volterra_identity_of_positive_sigma
      X q hq W hW hσ φ hφ hroot V hV a β K rfl rfl rfl
  obtain ⟨g, hgcont, hgC1, hgeq⟩ :=
    causal_gaussian_C1_volterra_resolvent_from_antitone_kernel
      K a β ha hKI.integrableOn hKpos hKA hKC
  exact ⟨a, β, K, g, ha, hKI.integrableOn, hgcont, hgC1, hVeq, hgeq⟩
