-- Prove2me | solution 1 for BianchiIX.gaussCylinderObservable_code
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T18:37:04.862192+00:00
-- url     : https://prove2.me/submissions/bbfa8ca0-1ad4-4d85-85a4-883237b34cc3

import Definitions.Def_BianchiIX_Statistics_GaussTypical
import Theorems.Thm_BianchiIX_gaussCode_mem_cylinder_iff
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
open InverseBranchTree.BranchEstimates


theorem solution (a : ℕ → ℕ+) (w : List ℕ) (hw : ∀ k ∈ w, 1 ≤ k) :
    gaussCylinderObservable w (gaussCode a) = if digitPrefix a w.length = w then 1 else 0 := by
  by_cases h : digitPrefix a w.length = w
  · have hc := (gaussCode_mem_cylinder_iff a w hw).mpr h
    simp [gaussCylinderObservable, hc, h]
  · have hc : gaussCode a ∉ gaussCylinder w :=
      fun hc => h ((gaussCode_mem_cylinder_iff a w hw).mp hc)
    simp [gaussCylinderObservable, hc, h]
