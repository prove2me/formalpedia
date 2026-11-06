-- Prove2me | solution 1 for BianchiIX.contDiff_rootCurveExtension
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:44:13.506041+00:00
-- url     : https://prove2.me/submissions/5b1c6ca4-d53e-4dfa-b7ca-33ea11f8160a

import Definitions.Def_BianchiIX_Analysis_RootCurveExtension
import Theorems.Thm_BianchiIX_continuous_rootCurveDerivative
import Theorems.Thm_BianchiIX_hasDerivAt_rootCurveExtension
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


theorem solution {l r : ℝ} (hlr : l < r) {f df : ℝ → ℝ}
    (hfl : 0 < f l) (hfr : 0 < f r)
    (hf : ∀ x ∈ Icc l r, HasDerivWithinAt f (df x) (Icc l r) x)
    (hdf : ContinuousOn df (Icc l r)) : ContDiff ℝ 1 (rootCurveExtension l r f df) := by
  rw [contDiff_one_iff_deriv]
  exact ⟨fun x => (hasDerivAt_rootCurveExtension hlr hfl hfr hf x).differentiableAt,
    (continuous_rootCurveDerivative hlr.le hdf).congr
      (fun x => (hasDerivAt_rootCurveExtension hlr hfl hfr hf x).deriv.symm)⟩
