-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_monotone_simple_weight_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:47:27.926199+00:00
-- url     : https://prove2.me/submissions/71444ade-5f4e-4736-a674-60a5abef237f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Exact nonnegative compensation is stable under monotone increase of
source-measurable weights, including infinite counts and rates. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Ω → ℝ≥0∞) (hN : Measurable N)
    (r : ℝ≥0∞) (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ n, Measurable (H n))
    (hmono : Monotone H)
    (hEach : ∀ n,
      (∫⁻ ω, H n ω * N ω ∂μ) = (∫⁻ ω, H n ω ∂μ) * r) :
    (∫⁻ ω, (⨆ n, H n ω) * N ω ∂μ) =
    (∫⁻ ω, ⨆ n, H n ω ∂μ) * r := by
  have hprod (n : ℕ) :
      Measurable (fun ω => H n ω * N ω) := (hH n).mul hN
  have hprodmono : Monotone (fun n ω => H n ω * N ω) := by
    intro i j hij ω
    calc
      H i ω * N ω = N ω * H i ω := mul_comm _ _
      _ ≤ N ω * H j ω := mul_le_mul_right ((hmono hij) ω) (N ω)
      _ = H j ω * N ω := mul_comm _ _
  calc
    (∫⁻ ω, (⨆ n, H n ω) * N ω ∂μ)
        = (∫⁻ ω, ⨆ n, H n ω * N ω ∂μ) := by
            congr 1
            funext ω
            exact ENNReal.iSup_mul (fun n => H n ω) (N ω)
    _ = ⨆ n, (∫⁻ ω, H n ω * N ω ∂μ) :=
          lintegral_iSup hprod hprodmono
    _ = ⨆ n, (∫⁻ ω, H n ω ∂μ) * r := by
          congr 1
          funext n
          exact hEach n
    _ = (⨆ n, (∫⁻ ω, H n ω ∂μ)) * r :=
          (ENNReal.iSup_mul _ r).symm
    _ = (∫⁻ ω, ⨆ n, H n ω ∂μ) * r := by
          rw [lintegral_iSup hH hmono]
