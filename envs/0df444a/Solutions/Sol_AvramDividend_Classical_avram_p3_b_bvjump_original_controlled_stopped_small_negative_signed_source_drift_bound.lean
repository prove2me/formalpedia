-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_controlled_stopped_small_negative_signed_source_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:34:10.743778+00:00
-- url     : https://prove2.me/submissions/816132a5-c723-45cc-9081-614b988612b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal Classical

/-- The signed discounted original stopped small-jump source compensator drift
has the same bounded first-order finite-variation envelope. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (w : ℝ → ℝ) (K : ℝ≥0) (a b q : ℝ)
    (hLip : LipschitzOnWith K w (Icc a b)) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Upre : ℝ≥0 × Ω → ℝ)
    (hUpre : ∀ p, Upre p = Function.leftLim
      (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)
    (E : Set (ℝ≥0 × Ω))
    (hE : ∀ p ∈ E, Upre p ∈ Icc (a + 1) b) :
    ∀ p : ℝ≥0 × Ω,
      |∫ z in Ioo (-1 : ℝ) 0,
        (if p ∈ E ∧ p.1 ≤ τ p.2 then
          Real.exp (-(q * (p.1 : ℝ))) *
            (w (Upre p + z) - w (Upre p)) else 0) ∂X.ν| ≤
      (if p ∈ E ∧ p.1 ≤ τ p.2 then
        (K : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, -z ∂X.ν) else 0) := by
  intro p
  by_cases hactive : p ∈ E ∧ p.1 ≤ τ p.2
  · simp only [if_pos hactive]
    exact (abs_integral_le_integral_abs).trans
      (avram_p3_b_bvjump_original_source_discounted_BV_small_absolute_drift_bound
        X hBV w K a b (Upre p) hLip (hE p hactive.1) q hq p.1)
  · simp only [if_neg hactive, integral_zero, abs_zero, le_refl]
