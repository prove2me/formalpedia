-- Prove2me | solution 1 for BianchiIX.rootCurveDerivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:40:39.449202+00:00
-- url     : https://prove2.me/submissions/7f611d26-3f48-4135-ad85-fffff15afc92

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Theorems.Thm_BianchiIX_rootCurveExtension_left
import Theorems.Thm_BianchiIX_rootCurveExtension_middle
import Theorems.Thm_BianchiIX_rootCurveExtension_right
import Theorems.Thm_BianchiIX_rootExtension_derivative_bound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter
open scoped Topology
open BianchiIX
noncomputable section


theorem solution {l r θ : ℝ} (hlr : l ≤ r) {f df : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < f x) (hd : ∀ x ∈ Icc l r, |df x| ≤ θ / 2)
    (x : ℝ) : |rootCurveDerivative l r f df x| ≤ θ / 2 := by
  by_cases hxl : x < l
  · rw [(rootCurveExtension_left f df hlr hxl.le).2]
    simpa only [neg_mul, one_mul] using
      rootExtension_derivative_bound (e := -1) (s := f l) (x := x - l)
        (hpos l ⟨le_rfl, hlr⟩) (by linarith) (hd l ⟨le_rfl, hlr⟩)
  by_cases hrx : r < x
  · rw [(rootCurveExtension_right f df hlr hrx.le).2]
    simpa only [one_mul] using
      rootExtension_derivative_bound (e := 1) (s := f r) (x := x - r)
        (hpos r ⟨hlr, le_rfl⟩) (by linarith) (hd r ⟨hlr, le_rfl⟩)
  have hx : x ∈ Icc l r := ⟨le_of_not_gt hxl, le_of_not_gt hrx⟩
  rw [(rootCurveExtension_middle f df hx).2]
  exact hd x hx
