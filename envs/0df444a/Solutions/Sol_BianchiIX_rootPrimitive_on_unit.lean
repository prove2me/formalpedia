-- Prove2me | solution 1 for BianchiIX.rootPrimitive_on_unit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:28:54.16511+00:00
-- url     : https://prove2.me/submissions/3833a5c7-49de-4ad0-8977-57b6e561fe97

import Definitions.Def_BianchiIX_Analysis_RootExtension
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


theorem solution {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    rootPrimitive t = t - t ^ 2 / 2 := by
  have heq : rootPrimitive t = ∫ u in (0 : ℝ)..t, (1 - u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact max_eq_left (by linarith [hu.2, ht.2])
  rw [heq]
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => v - v ^ 2 / 2) (1 - u) u := by
    convert! (hasDerivAt_id u).sub (((hasDerivAt_id u).pow 2).div_const 2) using 1
    simp
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((continuous_const.sub continuous_id).intervalIntegrable 0 t)
