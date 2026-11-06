-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_integrable_nonnegative_real_grid_to_ennreal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:55:37.686039+00:00
-- url     : https://prove2.me/submissions/1c0afdec-3562-47de-a4c6-cf7a1b8f5eca

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Transfer genuine real nonnegative integrable grid means to an
    ENNReal uniform budget without changing the grid payoffs. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (B : ℝ)
    (hInt : ∀ n, Integrable (F n) P)
    (hNonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hMean : ∀ n, (∫ ω, F n ω ∂P) ≤ B) :
    ∀ n : ℕ, (∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) ≤
      ENNReal.ofReal B := by
  intro n
  rw [← ofReal_integral_eq_lintegral_ofReal (hInt n) (hNonneg n)]
  exact ENNReal.ofReal_le_ofReal (hMean n)
