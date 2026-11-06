-- Prove2me | solution 1 for BianchiIX.rootExtension_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:47:04.746624+00:00
-- url     : https://prove2.me/submissions/8b7b2a16-270f-49e4-a947-a864660b44a8

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_rootExtension_bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set Filter MeasureTheory
open scoped Topology
open BianchiIX
noncomputable section


theorem solution {s d e x θ : ℝ} (hs : 0 < s) (he : |e| = 1)
    (hx : 0 ≤ e * x) (hd : |d| ≤ θ / 2) (hθ : θ ≤ 1) : 0 < rootExtension s d e x := by
  have hb := (rootExtension_bounds hs he hx hd).1
  have hfactor : 0 < 1 - θ / 4 := by linarith
  exact (mul_pos hfactor hs).trans_le hb
