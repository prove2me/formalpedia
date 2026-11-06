-- Prove2me | solution 1 for BianchiIX.gaussCylinder_distance_representative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:13:29.556361+00:00
-- url     : https://prove2.me/submissions/aae40972-629e-401a-b5ea-ec52dd46e931

import Definitions.Def_BianchiIX_Statistics_GaussContinuous
import Theorems.Thm_BianchiIX_gaussWord_diameter
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
import Mathlib.MeasureTheory.Function.LocallyIntegrable

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX
noncomputable section
open InverseBranchTree.BranchEstimates


theorem solution (n : ℕ) (w : GaussWords n)
    {x : ℝ} (hx : x ∈ gaussCylinder w.val) :
    |x - gaussRepresentative n w| ≤ (1 / 4 : ℝ) ^ (n / 2) := by
  obtain ⟨t, ht, rfl⟩ := hx
  simpa only [gaussRepresentative, w.property.1] using
    gaussWord_diameter w.val w.property.2 ⟨ht.1.le, ht.2.le⟩ ⟨le_rfl, zero_le_one⟩
