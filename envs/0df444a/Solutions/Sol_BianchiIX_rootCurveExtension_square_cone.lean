-- Prove2me | solution 1 for BianchiIX.rootCurveExtension_square_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:49:47.154936+00:00
-- url     : https://prove2.me/submissions/141d184c-1fc3-4d5b-90fc-e39f7a6c964c

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Theorems.Thm_BianchiIX_hasDerivAt_rootCurveExtension
import Theorems.Thm_BianchiIX_rootCurveDerivative_bound
import Theorems.Thm_BianchiIX_rootCurveExtension_pos
import Theorems.Thm_BianchiIX_square_derivative_cone
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


theorem solution {l r θ : ℝ} (hlr : l < r) {f df : ℝ → ℝ}
    (hpos : ∀ x ∈ Icc l r, 0 < f x) (hd : ∀ x ∈ Icc l r, |df x| ≤ θ / 2) (hθ : θ ≤ 1)
    (hf : ∀ x ∈ Icc l r, HasDerivWithinAt f (df x) (Icc l r) x) (x : ℝ) :
    |deriv (fun z => rootCurveExtension l r f df z ^ 2) x| ≤
      θ * Real.sqrt (rootCurveExtension l r f df x ^ 2) :=
  square_derivative_cone
    (hasDerivAt_rootCurveExtension hlr (hpos l ⟨le_rfl, hlr.le⟩) (hpos r ⟨hlr.le, le_rfl⟩) hf x)
    (rootCurveExtension_pos hlr.le hpos hd hθ x) (rootCurveDerivative_bound hlr.le hpos hd x)
