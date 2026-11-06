-- Prove2me | solution 1 for BianchiIX.normalizedMaxCurve_wall_sign
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:05:06.149423+00:00
-- url     : https://prove2.me/submissions/9fcedfa5-d42e-42c3-9771-437bb68a18a9

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set MeasureTheory


theorem solution {x₀ : NormalizedState}
    (hcon : stateConstraint x₀ = 1) {t₀ t : ℝ} (htt : t₀ ≤ t) (i : Fin 3) :
    (wallValue i (normalizedMaxCurve x₀ t₀ t) = 0 ↔ wallValue i x₀ = 0) ∧
      (0 ≤ wallValue i (normalizedMaxCurve x₀ t₀ t) ↔ 0 ≤ wallValue i x₀) := by
  let S := maximalNormalizedSolution x₀ t₀
  have ht : t ∈ S.domain := normalizedMaxDomain_contains_Ici_of_constraint hcon t₀ htt
  have H := normalized_wall_sign S.convex_domain S.isOpen_domain S.hasDerivAt S.initial_mem ht i
  rw [S.initial_eq] at H
  convert! H using 1
