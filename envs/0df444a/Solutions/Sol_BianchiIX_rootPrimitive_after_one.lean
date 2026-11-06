-- Prove2me | solution 1 for BianchiIX.rootPrimitive_after_one
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:36:11.212355+00:00
-- url     : https://prove2.me/submissions/d84c9a9b-70d2-486c-b83d-8e5f0165ce7c

import Definitions.Def_BianchiIX_Analysis_RootExtension
import Theorems.Thm_BianchiIX_continuous_rootCutoff
import Theorems.Thm_BianchiIX_rootPrimitive_on_unit
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


theorem solution {t : ℝ} (ht : 1 ≤ t) : rootPrimitive t = 1 / 2 := by
  have hzero : (∫ u in (1 : ℝ)..t, rootCutoff u) = 0 := by
    calc
      _ = ∫ _u in (1 : ℝ)..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht] at hu
        exact max_eq_right (by linarith [hu.1])
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (continuous_rootCutoff.intervalIntegrable (μ := volume) 0 1)
    (continuous_rootCutoff.intervalIntegrable (μ := volume) 1 t)
  change rootPrimitive 1 + _ = rootPrimitive t at hadd
  rw [hzero, rootPrimitive_on_unit ⟨by norm_num, le_rfl⟩] at hadd
  linarith
