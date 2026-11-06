-- Prove2me | solution 1 for BianchiIX.normalizedSectionFlux_flow
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:10:16.167998+00:00
-- url     : https://prove2.me/submissions/31f63a41-a349-4813-b024-e67f8cea913b

import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_hasDerivAt_stateConstraint
import Theorems.Thm_BianchiIX_normalizedConstraintVolume_flow
import Theorems.Thm_BianchiIX_normalizedFlowDifferential_field
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stateConstraint (x : NormalizedState) :
    HasFDerivAt stateConstraint (normalizedConstraintDifferential x) x :=
  ((contDiff_stateConstraint 1).differentiable (by norm_num) x).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedConstraintDifferential_field (x : NormalizedState) :
    normalizedConstraintDifferential x (normalizedField x) = 0 := by
  have hα := hasDerivAt_normalizedMaxCurve (initial_mem_normalizedMaxDomain x 0)
  have H := (hasFDerivAt_stateConstraint (normalizedMaxCurve x 0 0)).comp_hasDerivAt 0 hα
  simpa only [normalizedMaxCurve_initial] using H.unique (hasDerivAt_stateConstraint hα)

end
end

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1)
    (ht : t ∈ normalizedMaxDomain x t₀) (v : Fin 3 → NormalizedState)
    (hv : ∀ i, normalizedConstraintDifferential x (v i) = 0) :
    normalizedSectionFlux (normalizedMaxCurve x t₀ t)
        (fun i => normalizedFlowDifferential x t₀ t (v i)) =
      normalizedVolumeJacobian x t₀ t * normalizedSectionFlux x v := by
  let w : Fin 4 → NormalizedState := Fin.cons (normalizedField x) v
  have htan : ∀ i : Fin 4, normalizedConstraintDifferential x (w i) = 0 := by
    intro i
    exact Fin.cases (normalizedConstraintDifferential_field x) hv i
  have H := normalizedConstraintVolume_flow hpos hcon ht w htan
  have heq : (fun i : Fin 4 => normalizedFlowDifferential x t₀ t (w i)) =
      Fin.cons (normalizedField (normalizedMaxCurve x t₀ t))
        (fun i => normalizedFlowDifferential x t₀ t (v i)) := by
    funext i
    exact Fin.cases (normalizedFlowDifferential_field ht) (fun _ => rfl) i
  rw [heq] at H
  exact H
