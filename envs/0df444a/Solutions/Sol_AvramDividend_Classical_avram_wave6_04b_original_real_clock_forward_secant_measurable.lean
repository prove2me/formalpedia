-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04b_original_real_clock_forward_secant_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:53:16.764191+00:00
-- url     : https://prove2.me/submissions/6bcbdfd3-2f4c-463b-bfc2-2461edfd340a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_original_real_clock_postpayment_reserve_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The genuine original-source post-payment real-clock forward
secant integrand is Borel measurable whenever the extension V is Borel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q δ : ℝ) (V : ℝ → ℝ)
    (hVmeas : Measurable V) :
    Measurable (fun s : ℝ =>
      Real.exp (-(q * s)) *
        (δ + V (x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
          V ((x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω) + δ))) := by
  let F : ℝ → ℝ := fun s =>
    x + X.X s.toNNReal ω - rightLimit D s.toNNReal ω
  have hF : Measurable F :=
    avram_wave6_04b_original_real_clock_postpayment_reserve_measurable
      X x D hD ω
  have hExp : Measurable (fun s : ℝ => Real.exp (-(q * s))) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul measurable_id).neg)
  have hVf : Measurable (fun s : ℝ => V (F s)) :=
    hVmeas.comp hF
  have hVfd : Measurable (fun s : ℝ => V (F s + δ)) :=
    hVmeas.comp (hF.add measurable_const)
  change Measurable (fun s : ℝ =>
    Real.exp (-(q * s)) * (δ + V (F s) - V (F s + δ)))
  exact hExp.mul ((measurable_const.add hVf).sub hVfd)
