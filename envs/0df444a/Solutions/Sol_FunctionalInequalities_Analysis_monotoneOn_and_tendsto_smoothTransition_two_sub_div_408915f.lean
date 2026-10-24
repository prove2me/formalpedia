-- Prove2me | solution 1 for FunctionalInequalities.Analysis.monotoneOn_and_tendsto_smoothTransition_two_sub_div_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:40:00.858619+00:00
-- url     : https://prove2.me/submissions/01ac9240-9328-48bd-800f-c6b7609a03bc

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Real-parameter monotone exhaustion** (Letwin Lemma A.4, p. 17, `χ_R ↑ 1` for real `R`): for every real `a`,
`R ↦ η(a/R)` is monotone on `(0, ∞)` and tends to `1` at `atTop`, for `η t = smoothTransition (2 − t)`. -/
theorem solution (a : ℝ) :
    MonotoneOn (fun R : ℝ => Real.smoothTransition (2 - a / R)) (Set.Ioi 0) ∧
      Filter.Tendsto (fun R : ℝ => Real.smoothTransition (2 - a / R)) Filter.atTop (nhds 1) := by
    constructor
    · intro x hx y hy hxy
      change 0 < x at hx
      change 0 < y at hy
      by_cases ha : a < 0
      · have hax : a / x < 0 := div_neg_of_neg_of_pos ha hx
        have hay : a / y < 0 := div_neg_of_neg_of_pos ha hy
        have hxval : Real.smoothTransition (2 - a / x) = 1 :=
          Real.smoothTransition.one_of_one_le (by linarith)
        have hyval : Real.smoothTransition (2 - a / y) = 1 :=
          Real.smoothTransition.one_of_one_le (by linarith)
        change Real.smoothTransition (2 - a / x) ≤ Real.smoothTransition (2 - a / y)
        rw [hxval, hyval]
      · have ha0 : 0 ≤ a := le_of_not_gt ha
        have hquot : a / y ≤ a / x := by
          apply (div_le_div_iff₀ hy hx).2
          exact mul_le_mul_of_nonneg_left hxy ha0
        have harg : 2 - a / x ≤ 2 - a / y := by
          linarith
        exact Real.smoothTransition.monotone harg
    · have h_inv :
          Filter.Tendsto (fun R : ℝ => R⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero
      have hmul :
          Filter.Tendsto (fun R : ℝ => a * R⁻¹) Filter.atTop (nhds (a * 0)) :=
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => a) Filter.atTop (nhds a)).mul h_inv
      have hdiv :
          Filter.Tendsto (fun R : ℝ => a / R) Filter.atTop (nhds 0) := by
        simpa [div_eq_mul_inv] using hmul
      have hbelow : Set.Iio (1 : ℝ) ∈ nhds (0 : ℝ) :=
        Iio_mem_nhds (by norm_num)
      have hevent : ∀ᶠ R : ℝ in Filter.atTop, a / R < 1 := by
        simpa only [Set.mem_Iio] using hdiv.eventually hbelow
      have heq :
          (fun R : ℝ => Real.smoothTransition (2 - a / R)) =ᶠ[Filter.atTop]
            (fun _ : ℝ => (1 : ℝ)) := by
        filter_upwards [hevent] with R hR
        apply Real.smoothTransition.one_of_one_le
        linarith
      exact
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).congr'
          heq.symm
