-- Prove2me | solution 1 for BianchiIX.gaussWords_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T19:10:07.90874+00:00
-- url     : https://prove2.me/submissions/a8f7be24-73fc-45f2-b498-2aa27fb1bb37

import Definitions.Def_BianchiIX_Statistics_GaussPartition
import Theorems.Thm_BianchiIX_gaussCylinder_comparable
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
    Pairwise (fun v w : GaussWords n => Disjoint (gaussCylinder v.val) (gaussCylinder w.val)) := by
  intro v w hvw
  apply disjoint_left.mpr
  intro x hxv hxw
  have hc := gaussCylinder_comparable v.property.2 w.property.2 ⟨x, hxv, hxw⟩
  have hlen := v.property.1.trans w.property.1.symm
  exact hvw (Subtype.ext (hc.elim (fun h => h.eq_of_length hlen)
    (fun h => (h.eq_of_length hlen.symm).symm)))
