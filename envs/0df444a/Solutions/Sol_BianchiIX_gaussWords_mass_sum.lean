-- Prove2me | solution 1 for BianchiIX.gaussWords_mass_sum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:18:40.412238+00:00
-- url     : https://prove2.me/submissions/29ca9d39-7f75-47bd-a6d8-263e9638c66b

import Definitions.Def_BianchiIX_Statistics_GaussPartition
import Theorems.Thm_BianchiIX_ae_gaussWords_cover
import Theorems.Thm_BianchiIX_gaussWords_disjoint
import Theorems.Thm_BianchiIX_measurableSet_gaussCylinder
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


theorem solution (n : ℕ) :
    (∑' w : GaussWords n, gaussMeasure (gaussCylinder w.val)) = 1 := by
  rw [← measure_iUnion (gaussWords_disjoint n) (fun w => measurableSet_gaussCylinder w.val)]
  have heq : (⋃ w : GaussWords n, gaussCylinder w.val) =ᵐ[gaussMeasure] univ := by
    filter_upwards [ae_gaussWords_cover n] with x hx
    exact propext (iff_true_intro hx)
  simpa only [gaussMeasure_univ] using measure_congr heq
