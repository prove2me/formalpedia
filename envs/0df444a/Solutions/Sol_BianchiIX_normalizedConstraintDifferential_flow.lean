-- Prove2me | solution 1 for BianchiIX.normalizedConstraintDifferential_flow
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:26:02.521384+00:00
-- url     : https://prove2.me/submissions/f38aec0c-bdda-4e46-a657-a42e8ad01145

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.isOpen_normalizedFlowDomain (t₀ : ℝ) : IsOpen (normalizedFlowDomain t₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact mem_interior_iff_mem_nhds.mp (normalizedMaxCurve_regular hz).1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

private theorem BianchiIX.hasFDerivAt_stateConstraint (x : NormalizedState) :
    HasFDerivAt stateConstraint (normalizedConstraintDifferential x) x :=
  ((contDiff_stateConstraint 1).differentiable (by norm_num) x).hasFDerivAt

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    (normalizedConstraintDifferential (normalizedMaxCurve x t₀ t)).comp
      (normalizedFlowDifferential x t₀ t) = normalizedConstraintDifferential x := by
  have hd := (hasFDerivAt_stateConstraint (normalizedMaxCurve x t₀ t)).comp x
    (hasFDerivAt_normalizedMaxCurve_initial ht)
  have heq : stateConstraint =ᶠ[𝓝 x] (fun y => stateConstraint (normalizedMaxCurve y t₀ t)) := by
    have hc : ContinuousAt (fun y : NormalizedState => (y, t)) x := by fun_prop
    filter_upwards [hc.eventually ((isOpen_normalizedFlowDomain t₀).mem_nhds ht)] with y hy
    exact (normalizedMaxCurve_constraint hy).symm
  exact (hd.congr_of_eventuallyEq heq).unique (hasFDerivAt_stateConstraint x)
