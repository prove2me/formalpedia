-- Prove2me | solution 1 for AvramDividend.Classical.levy_finite_state_semigroup_budget_of_generator_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:36:19.69181+00:00
-- url     : https://prove2.me/submissions/33c04ad0-c6e6-42cb-bc0f-3293d5333429

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_discounted_semigroup_le_of_generator_derivative
import Mathlib.Analysis.Calculus.FDeriv.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Statewise discounted Levy semigroup comparison from generator control. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (u a : ι → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (F : ι → ℝ → ℝ)
    (hF0 : ∀ i, F i 0 = w (u i - a i))
    (hFcont : ∀ i, ContinuousOn (F i) (Ici 0))
    (hFdiff : ∀ i s, 0 < s → DifferentiableAt ℝ (F i) s)
    (hFtrans : ∀ i s, 0 ≤ s →
      F i s = ∫ ω, w (u i - a i + X.X (Real.toNNReal s) ω) ∂P)
    (hFderiv : ∀ i s, 0 < s →
      deriv (F i) s = ∫ ω,
        X.generator w (u i - a i + X.X (Real.toNNReal s) ω) ∂P)
    (hIntW : ∀ i s, 0 < s → Integrable
      (fun ω => w (u i - a i + X.X (Real.toNNReal s) ω)) P)
    (hIntGen : ∀ i s, 0 < s → Integrable
      (fun ω => X.generator w (u i - a i + X.X (Real.toNNReal s) ω)) P)
    (hHJB : ∀ y : ℝ, X.generator w y ≤ q * w y)
    (t : ℝ) (ht : 0 ≤ t) :
    ∀ i,
      Real.exp (-(q * t)) *
        (∫ ω, w (u i - a i + X.X (Real.toNNReal t) ω) ∂P) ≤
      w (u i - a i) := by
  intro i
  have h := levy_discounted_semigroup_le_of_generator_derivative
    X w q (u i - a i) (F i)
    (hFcont i) (hFdiff i) (fun s hs => hFtrans i s (le_of_lt hs))
    (hFderiv i) (hIntW i) (hIntGen i) hHJB t ht
  simpa only [hFtrans i t ht, hF0 i] using h
