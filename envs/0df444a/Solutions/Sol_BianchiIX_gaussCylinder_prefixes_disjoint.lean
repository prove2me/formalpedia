-- Prove2me | solution 1 for BianchiIX.gaussCylinder_prefixes_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:03:51.10116+00:00
-- url     : https://prove2.me/submissions/13ac53c2-1762-4818-b328-d1ec93164838

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Theorems.Thm_BianchiIX_gaussCylinder_comparable
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

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal


theorem solution {ι : Type*} (a : ι → ℕ → ℕ+) (n : ℕ)
    (hunique : Function.Injective (fun i => digitPrefix (a i) n)) :
    Pairwise (fun i j => Disjoint (gaussCylinder (digitPrefix (a i) n))
      (gaussCylinder (digitPrefix (a j) n))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hc := gaussCylinder_comparable (digitPrefix_positive (a i) n)
    (digitPrefix_positive (a j) n) ⟨x, hxi, hxj⟩
  have hlen : (digitPrefix (a i) n).length = (digitPrefix (a j) n).length := by
    simp only [digitPrefix_length]
  exact hij (hunique (hc.elim (fun h => h.eq_of_length hlen)
    (fun h => (h.eq_of_length hlen.symm).symm)))
