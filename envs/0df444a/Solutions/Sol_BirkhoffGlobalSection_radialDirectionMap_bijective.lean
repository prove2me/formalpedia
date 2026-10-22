-- Prove2me | solution 1 for BirkhoffGlobalSection.radialDirectionMap_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:40:05.948568+00:00
-- url     : https://prove2.me/submissions/01cb000f-27bf-4102-8d82-87823d8a8937

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

theorem solution (S : Set Phase) (hsne : ∀ s ∈ S, s ≠ 0)
    (hray : ∀ x : Phase, ‖x‖ = 1 → ∃ r : ℝ, 0 < r ∧ r • x ∈ S)
    (huniq : ∀ x : Phase, ‖x‖ = 1 → ∀ r t : ℝ, 0 < r → 0 < t →
      r • x ∈ S → t • x ∈ S → r = t) :
    Function.Bijective ((fun s : S => (⟨normalize (s : Phase), norm_normalize (hsne s s.property)⟩ : ({x : Phase // ‖x‖ = 1})))) := by
  constructor
  · intro s t hst
    have heq : normalize (s : Phase) = normalize (t : Phase) := congrArg Subtype.val hst
    have hspos : 0 < ‖(s : Phase)‖ := norm_pos_iff.mpr (hsne s s.property)
    have htpos : 0 < ‖(t : Phase)‖ := norm_pos_iff.mpr (hsne t t.property)
    have hnr : ‖(s : Phase)‖ = ‖(t : Phase)‖ :=
      huniq (normalize (s : Phase)) (norm_normalize (hsne s s.property))
        ‖(s : Phase)‖ ‖(t : Phase)‖ hspos htpos
        (by simpa only [norm_smul_normalize] using s.property)
        (by rw [heq]; simpa only [norm_smul_normalize] using t.property)
    apply Subtype.ext
    calc
      (s : Phase) = ‖(s : Phase)‖ • normalize (s : Phase) := (norm_smul_normalize _).symm
      _ = ‖(t : Phase)‖ • normalize (t : Phase) := by rw [hnr, heq]
      _ = (t : Phase) := norm_smul_normalize _
  · intro x
    obtain ⟨r, hr, hrs⟩ := hray x x.property
    refine ⟨⟨r • (x : Phase), hrs⟩, ?_⟩
    apply Subtype.ext
    exact (normalize_smul_of_pos hr _).trans (normalize_eq_self_of_norm_eq_one x.property)
