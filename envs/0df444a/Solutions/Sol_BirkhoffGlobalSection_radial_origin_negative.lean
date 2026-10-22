-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_origin_negative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:04.310778+00:00
-- url     : https://prove2.me/submissions/115199bd-a723-497f-81a4-05984f694ef0

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue


open BirkhoffGlobalSection


open BirkhoffGlobalSection NormedSpace Set Metric Filter
open scoped Topology unitInterval BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem solution (F : Phase → ℝ) (S : Set Phase)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    F 0 < 0 := by
  let e : Phase := fun i => if i = 0 then 1 else 0
  have he : e ∈ unitThreeSphere := by
    have h10 : (1 : Fin 4) ≠ 0 := by decide
    have h20 : (2 : Fin 4) ≠ 0 := by decide
    have h30 : (3 : Fin 4) ≠ 0 := by decide
    norm_num [e, unitThreeSphere, zNormSq, wNormSq, h10, h20, h30]
  obtain ⟨R, hR, hRS⟩ := hray e he
  have hezero : (fun _ : Fin 4 => (0 : ℝ)) = (0 : Phase) := rfl
  simpa only [zero_mul, hezero] using hneg e he R hR hRS 0 le_rfl hR
