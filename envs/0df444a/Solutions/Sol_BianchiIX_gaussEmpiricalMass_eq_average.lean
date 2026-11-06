-- Prove2me | solution 1 for BianchiIX.gaussEmpiricalMass_eq_average
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:14:01.382235+00:00
-- url     : https://prove2.me/submissions/575c6ba2-61f6-4d51-bd4f-66f1e34ab9b3

import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Definitions.Def_BianchiIX_Statistics_GaussPartition
import Theorems.Thm_BianchiIX_gaussCylinderObservable_code
import Theorems.Thm_BianchiIX_gaussMap_iterate_code
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
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section


theorem solution (a : ℕ → ℕ+) (n N : ℕ) (w : GaussWords n) :
    gaussEmpiricalMass a n N w =
      birkhoffAverage ℝ gaussMap (gaussCylinderObservable w.val) (N + 1) (gaussCode a) := by
  classical
  change ((N + 1 : ℕ) : ℝ)⁻¹ * _ = ((N + 1 : ℕ) : ℝ)⁻¹ * _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussMap_iterate_code, gaussCylinderObservable_code _ w.val w.property.2]
  simp only [gaussPrefixWord, Subtype.ext_iff, w.property.1, eq_comm]
