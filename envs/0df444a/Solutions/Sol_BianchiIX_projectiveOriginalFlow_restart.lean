-- Prove2me | solution 1 for BianchiIX.projectiveOriginalFlow_restart
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:00:39.134191+00:00
-- url     : https://prove2.me/submissions/01e8c4ce-d1cc-435e-892e-ab5f32b3e6ca

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

/-- Restart at a regular projective state uses the same original Einstein time. -/
theorem solution {y : ProjectiveState} {s t : ℝ}
    (hD : 0 < projectiveStateDenom y) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 s 0) :
    projectiveOriginalFlow (projectiveOriginalFlow y 0 s) 0 t = projectiveOriginalFlow y 0 (t + s) := by
  have hc := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hreconstruct := fromProjectiveState_toProjectiveState (ne_of_gt hA)
    ((normalizedMaxCurve_constraint hdom).trans hc)
  have H := normalizedMaxCurve_shift
    (by simpa only [zero_add] using hdom)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht hs))
  simp only [zero_add] at H
  change toProjectiveState (normalizedMaxCurve
    (fromProjectiveState (toProjectiveState (normalizedMaxCurve (fromProjectiveState y) 0 s))) 0 t) = _
  rw [hreconstruct, H]
  rfl
