-- Prove2me | solution 1 for BianchiIX.gaussTailObservable_succ_code
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:43:43.923372+00:00
-- url     : https://prove2.me/submissions/a8587378-11bb-4c1e-a98b-60f165f29c0a

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussDigits
import Theorems.Thm_BianchiIX_gaussCylinderObservable_code
import Theorems.Thm_BianchiIX_gaussTailObservable_code
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

private theorem BianchiIX.nat_tail_step (m k : ℕ) :
    (if k + 1 ≤ m then (1 : ℝ) else 0) =
      (if k ≤ m then 1 else 0) - (if m = k then 1 else 0) := by
  by_cases he : m = k
  · subst m
    simp
  · by_cases h : k ≤ m
    · simp [he, h, show k + 1 ≤ m by omega]
    · simp [he, h, show ¬ k + 1 ≤ m by omega]

theorem solution (a : ℕ → ℕ+) (k : ℕ+) :
    gaussTailObservable (k + 1) (gaussCode a) =
      gaussTailObservable k (gaussCode a) - gaussCylinderObservable [(k : ℕ)] (gaussCode a) := by
  rw [gaussTailObservable_code, gaussTailObservable_code,
    gaussCylinderObservable_code _ _ (by simpa using Nat.succ_le_of_lt k.pos)]
  simpa [digitPrefix] using nat_tail_step (a 0) k
