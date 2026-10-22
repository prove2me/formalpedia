-- Prove2me | solution 1 for AvramDividend.Classical.levy_transition_random_reserve_integrable_difference_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:51:59.311031+00:00
-- url     : https://prove2.me/submissions/250dbf12-6fd5-4e4f-9a71-90b32f803275

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_transition_preserves_lipschitz_bound
import Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_stronglyMeasurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (f : ℝ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ u : ℝ, Integrable
      (fun η => f (u + X.X t η)) P)
    (Z₁ Z₂ : Ω → ℝ) (hZ₁ : Measurable Z₁)
    (hZ₂ : Measurable Z₂)
    (hDom : Integrable (fun ω => L * |Z₁ ω - Z₂ ω|) P) :
    Integrable (fun ω =>
      (∫ η, f (Z₁ ω + X.X t η) ∂P) -
      (∫ η, f (Z₂ ω + X.X t η) ∂P)) P := by
  have hTM₁ := levy_transition_random_reserve_stronglyMeasurable
    X t f L hL hLip hInt Z₁ hZ₁
  have hTM₂ := levy_transition_random_reserve_stronglyMeasurable
    X t f L hL hLip hInt Z₂ hZ₂
  apply hDom.mono (hTM₁.sub hTM₂).aestronglyMeasurable
  filter_upwards [] with ω
  have hb := levy_transition_preserves_lipschitz_bound
    X t f L hL hLip hInt (Z₁ ω) (Z₂ ω)
  change
    ‖(∫ η, f (Z₁ ω + X.X t η) ∂P) -
      (∫ η, f (Z₂ ω + X.X t η) ∂P)‖ ≤
    ‖L * |Z₁ ω - Z₂ ω|‖
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hL, abs_abs]
    using hb
