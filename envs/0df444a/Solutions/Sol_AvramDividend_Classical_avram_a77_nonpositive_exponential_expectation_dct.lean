-- Prove2me | solution 1 for AvramDividend.Classical.avram_a77_nonpositive_exponential_expectation_dct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:17:58.075912+00:00
-- url     : https://prove2.me/submissions/49e1fb05-6194-4d99-87c1-4c6b6e2f992a

/- Bounded source physical negative-mark exponent DCT.
   Every approximate exponential has norm at most one almost everywhere,
   yielding the exact source E exp(mark sum) limit by Mathlib DCT. -/
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (J : Ω → ℝ)
    (hMeas : ∀ n, Measurable (f n))
    (hLimit : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (J ω)))
    (hNonpos : ∀ᵐ ω ∂P, ∀ n, f n ω ≤ 0) :
    Tendsto (fun n => ∫ ω, Real.exp (f n ω) ∂P)
      atTop (𝓝 (∫ ω, Real.exp (J ω) ∂P)) := by
  have hBound : ∀ n, ∀ᵐ ω ∂P, ‖Real.exp (f n ω)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards [hNonpos] with ω hω
    have hb : Real.exp (f n ω) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (hω n)
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hb
  have hExpLimit :
      ∀ᵐ ω ∂P,
        Tendsto (fun n => Real.exp (f n ω)) atTop
          (𝓝 (Real.exp (J ω))) := by
    filter_upwards [hLimit] with ω hω
    exact (Real.continuous_exp.tendsto (J ω)).comp hω
  exact tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun n => (hMeas n).exp.aestronglyMeasurable)
    (integrable_const _) hBound hExpLimit

