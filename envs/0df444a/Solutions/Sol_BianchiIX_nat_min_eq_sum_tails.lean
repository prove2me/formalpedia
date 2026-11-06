-- Prove2me | solution 1 for BianchiIX.nat_min_eq_sum_tails
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:36:24.825223+00:00
-- url     : https://prove2.me/submissions/b3e90844-f6f4-4439-afb0-fcbc4390ef99

import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section


theorem solution (m R : ℕ) :
    min (m : ℝ) (R : ℝ) = ∑ j ∈ Finset.range R, if j + 1 ≤ m then (1 : ℝ) else 0 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ← ih]
    by_cases h : R < m
    · have hR : (R : ℝ) ≤ m := by exact_mod_cast h.le
      have hR' : (R : ℝ) + 1 ≤ m := by exact_mod_cast h
      simp [min_eq_right hR, min_eq_right hR', Nat.succ_le_iff.mpr h]
    · have hm : (m : ℝ) ≤ R := by exact_mod_cast le_of_not_gt h
      have hm' : (m : ℝ) ≤ (R : ℝ) + 1 := by linarith
      simp [min_eq_left hm, min_eq_left hm', show ¬ R + 1 ≤ m by omega]
