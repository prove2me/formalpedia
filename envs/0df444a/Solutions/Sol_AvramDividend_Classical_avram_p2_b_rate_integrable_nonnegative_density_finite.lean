-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_integrable_nonnegative_density_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:28:54.150204+00:00
-- url     : https://prove2.me/submissions/d08d2046-5595-4d1a-b58a-f47f5a3ff3d9

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ)
    (hf : Integrable f μ)
    (hn : ∀ᵐ ω ∂μ, 0 ≤ f ω) :
    (μ.withDensity (fun ω => ENNReal.ofReal (f ω))) Set.univ < ⊤ := by
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf hn]
  exact ENNReal.ofReal_lt_top
