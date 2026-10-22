-- Prove2me | solution 1 for AvramDividend.Classical.chat06_negative_mark_moment_between_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:39:26.109688+00:00
-- url     : https://prove2.me/submissions/dfe34199-0d84-49a7-8d9a-e1532728d8a3

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Real

namespace AvramChat06

/-- For θ≥0 and nonpositive marks, the Laplace moment exists and
lies in [0,1]. These are precisely the bounds required to dominate
the random-count Poisson mixing term m^N. -/
theorem negative_mark_moment_between_zero_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (hneg : ∀ᵐ ω ∂P, Y ω ≤ 0)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp (θ * Y ω)) P ∧
      0 ≤ (∫ ω, Real.exp (θ * Y ω) ∂P) ∧
      (∫ ω, Real.exp (θ * Y ω) ∂P) ≤ 1 := by
  have he : Measurable (fun ω => Real.exp (θ * Y ω)) := by
    fun_prop
  have hbd : ∀ᵐ ω ∂P, ‖Real.exp (θ * Y ω)‖ ≤ 1 := by
    filter_upwards [hneg] with ω hω
    have hp : θ * Y ω ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hθ hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr hp
  have hint : Integrable (fun ω => Real.exp (θ * Y ω)) P :=
    (integrable_const (1 : ℝ)).mono'
      he.aestronglyMeasurable hbd
  have hzero : 0 ≤ ∫ ω, Real.exp (θ * Y ω) ∂P :=
    integral_nonneg fun ω => (Real.exp_pos _).le
  have hupper : (∫ ω, Real.exp (θ * Y ω) ∂P) ≤ 1 := by
    have hle : (∫ ω, Real.exp (θ * Y ω) ∂P) ≤
        (∫ _ : Ω, (1 : ℝ) ∂P) :=
      integral_mono_ae hint (integrable_const 1)
        (by filter_upwards [hneg] with ω hω
            exact Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonneg_of_nonpos hθ hω))
    simpa using hle
  exact ⟨hint, hzero, hupper⟩

end AvramChat06

open AvramChat06

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : Measurable Y)
    (hneg : ∀ᵐ ω ∂P, Y ω ≤ 0)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp (θ * Y ω)) P ∧
      0 ≤ (∫ ω, Real.exp (θ * Y ω) ∂P) ∧
      (∫ ω, Real.exp (θ * Y ω) ∂P) ≤ 1 := by
  exact negative_mark_moment_between_zero_one P Y hY hneg θ hθ
