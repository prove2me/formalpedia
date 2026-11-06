-- Prove2me | solution 1 for BianchiIX.scaled_core_return_isLeast
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:11:26.355942+00:00
-- url     : https://prove2.me/submissions/fb44f7c8-bb5b-4111-87bc-c20ecf2a08eb

import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_scaled_core_interior_above
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution {β : ℝ → ProjectiveState} {a : ℝ → ℝ} {k s t : ℝ}
    (hk : 6 ≤ k) (hst : s < t)
    (ha : ∀ u ∈ Icc s t, 0 < a u)
    (hβ : ∀ u ∈ Icc s t, HasDerivAt β (a u • projectiveField (β u)) u)
    (hr : ∀ u ∈ Icc s t, 99 / 100 * k ≤ coreRadius (β u 0) (β u 2))
    (hv : ∀ u ∈ Icc s t, 1 ≤ β u 2)
    (hu : ∀ u ∈ Icc s t, 0 ≤ β u 1 ∧ β u 1 ≤ (1 / 10000) / k)
    (hw : ∀ u ∈ Icc s t, 0 ≤ β u 3 ∧ β u 3 ≤ (1 / 10000) / k)
    (hvt : β t 2 = 1) : IsLeast {u | s < u ∧ β u 2 = 1} t := by
  refine ⟨⟨hst, hvt⟩, ?_⟩
  intro u hu'
  by_contra! hut
  have H := scaled_core_interior_above hk ha hβ hr hv hu hw u ⟨hu'.1, hut⟩
  rw [hu'.2] at H
  exact (lt_irrefl (1 : ℝ)) H
