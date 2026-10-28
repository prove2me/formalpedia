-- Prove2me | solution 1 for AvramDividend.Classical.levy_discounted_semigroup_le_of_generator_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:24:13.914983+00:00
-- url     : https://prove2.me/submissions/71731cac-74e5-405d-99e3-59e15e4613f1

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

/-! Convert the pointwise generator inequality to a discounted semigroup bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (q x : ℝ) (f : ℝ → ℝ)
    (hfcont : ContinuousOn f (Ici 0))
    (hfdiff : ∀ s : ℝ, 0 < s → DifferentiableAt ℝ f s)
    (hftrans : ∀ s : ℝ, 0 < s →
      f s = ∫ ω, w (x + X.X (Real.toNNReal s) ω) ∂P)
    (hfderiv : ∀ s : ℝ, 0 < s →
      deriv f s = ∫ ω,
        X.generator w (x + X.X (Real.toNNReal s) ω) ∂P)
    (hIntW : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => w (x + X.X (Real.toNNReal s) ω)) P)
    (hIntGen : ∀ s : ℝ, 0 < s → Integrable
      (fun ω => X.generator w (x + X.X (Real.toNNReal s) ω)) P)
    (hHJB : ∀ y : ℝ, X.generator w y ≤ q * w y)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-(q * t)) * f t ≤ f 0 := by
  have hderiv_le : ∀ s : ℝ, 0 < s → deriv f s ≤ q * f s := by
    intro s hs
    rw [hfderiv s hs, hftrans s hs]
    calc
      (∫ ω, X.generator w (x + X.X (Real.toNNReal s) ω) ∂P) ≤
        (∫ ω, q * w (x + X.X (Real.toNNReal s) ω) ∂P) := by
          apply integral_mono (hIntGen s hs) ((hIntW s hs).const_mul q)
          intro ω
          exact hHJB (x + X.X (Real.toNNReal s) ω)
      _ = q * (∫ ω, w (x + X.X (Real.toNNReal s) ω) ∂P) := by
        rw [integral_const_mul]
  exact levy_discounted_semigroup_le_initial_of_deriv_le
    f q hfcont hfdiff hderiv_le t ht
