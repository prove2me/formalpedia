-- Prove2me | solution 1 for AvramDividend.Classical.levy_killed_discounted_expectation_le_of_local_generator_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:19:14.863012+00:00
-- url     : https://prove2.me/submissions/3f2bc93b-d7b0-4dad-b3ab-0d62c446848a

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_initial_of_deriv_le
import Mathlib.Analysis.Calculus.FDeriv.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! A killed semigroup uses HJB control only on its surviving states. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q : ℝ) (z : ℝ → Ω → ℝ)
    (active : ℝ → Ω → Bool) (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Ici 0))
    (hfdiff : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ f s)
    (hftrans : ∀ s : ℝ, 0 < s →
      f s = ∫ ω, if active s ω then w (z s ω) else 0 ∂P)
    (hfderiv : ∀ s : ℝ, 0 < s →
      deriv f s = ∫ ω,
        if active s ω then X.generator w (z s ω) else 0 ∂P)
    (hIntW : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => if active s ω then w (z s ω) else 0) P)
    (hIntGen : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => if active s ω then X.generator w (z s ω) else 0) P)
    (hHJB : ∀ s : ℝ, 0 < s → ∀ ω, active s ω = true →
      X.generator w (z s ω) ≤ q * w (z s ω))
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(q * t)) * f t ≤ f 0 := by
  have hderiv : ∀ s : ℝ, 0 < s → deriv f s ≤ q * f s := by
    intro s hs
    rw [hfderiv s hs, hftrans s hs]
    calc
      (∫ ω, if active s ω then X.generator w (z s ω) else 0 ∂P) ≤
        (∫ ω, q * (if active s ω then w (z s ω) else 0) ∂P) := by
          apply integral_mono (hIntGen s hs) ((hIntW s hs).const_mul q)
          intro ω
          cases h : active s ω with
          | false => simp [h]
          | true => simpa [h] using hHJB s hs ω h
      _ = q * (∫ ω, if active s ω then w (z s ω) else 0 ∂P) := by
          rw [integral_const_mul]
  exact levy_discounted_semigroup_le_initial_of_deriv_le
    f q hfcont hfdiff hderiv t ht
