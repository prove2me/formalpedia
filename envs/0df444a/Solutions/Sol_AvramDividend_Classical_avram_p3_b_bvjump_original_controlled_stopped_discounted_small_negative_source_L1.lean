-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_stopped_discounted_small_negative_source_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:26:40.569232+00:00
-- url     : https://prove2.me/submissions/bcd8ae8d-12dc-41e2-8b3f-d3c768dbf636

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_pre_source_small_negative_nonlin_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal Classical

/-- At the actual bounded stopping clock, the original controlled reserve's
discounted nonlinear source small-negative-jump kernel is ν-integrable. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b q : ℝ)
    (hLip : LipschitzOnWith K w (Icc a b))
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E, Upre p ∈ Icc (a + 1) b) :
    ∀ p : ℝ≥0 × Ω, IntegrableOn (fun z : ℝ =>
      if p ∈ E ∧ p.1 ≤ τ p.2 then
        Real.exp (-(q * (p.1 : ℝ))) *
          (w (Upre p + z) - w (Upre p)) else 0)
      (Ioo (-1 : ℝ) 0) X.ν := by
  intro p
  change Integrable (fun z : ℝ =>
    if p ∈ E ∧ p.1 ≤ τ p.2 then
      Real.exp (-(q * (p.1 : ℝ))) *
        (w (Upre p + z) - w (Upre p)) else 0)
    (X.ν.restrict (Ioo (-1 : ℝ) 0))
  by_cases hactive : p ∈ E ∧ p.1 ≤ τ p.2
  · have hbase :=
      avram_p3_b_bvjump_original_controlled_pre_source_small_negative_nonlin_L1
        X hBV D hD x w K a b hLip Upre hUpre E hE p hactive.1
    simpa [hactive] using
      hbase.const_mul (Real.exp (-(q * (p.1 : ℝ))))
  · simpa [hactive] using
      (integrable_zero : Integrable (fun _ : ℝ => (0 : ℝ))
        (X.ν.restrict (Ioo (-1 : ℝ) 0)))
