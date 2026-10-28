-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_exp_deficit_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:47:14.539951+00:00
-- url     : https://prove2.me/submissions/a9f47144-bbdb-4a5c-8140-21350b9e73d9

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
open MeasureTheory
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (D : Ω → ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ D ω)
    (hMeas : AEStronglyMeasurable
      (fun ω => (1 : ℝ) - Real.exp (-θ * D ω)) P) :
    Integrable (fun ω => (1 : ℝ) - Real.exp (-θ * D ω)) P := by
  refine Integrable.of_bound hMeas 1 ?_
  filter_upwards [hNonneg] with ω hω
  have h1 : -θ * D ω ≤ 0 := by nlinarith
  have h2 := Real.exp_le_one_iff.mpr h1
  have h3 := Real.exp_pos (-θ * D ω)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith
