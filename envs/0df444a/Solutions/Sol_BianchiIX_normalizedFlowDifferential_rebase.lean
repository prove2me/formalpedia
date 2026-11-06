-- Prove2me | solution 1 for BianchiIX.normalizedFlowDifferential_rebase
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:26:00.523018+00:00
-- url     : https://prove2.me/submissions/c8e6c98f-06e2-46b5-878e-ad67994509df

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowComposition
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxDomain_rebase
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
open Set Filter Metric
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_rebase {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (normalizedMaxCurve x t₀ s) s t = normalizedMaxCurve x t₀ t :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).rebase hs) ht

end
end

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

/-- Differentiating the actual restart identity gives the variational cocycle. -/
theorem solution {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    (normalizedFlowDifferential (normalizedMaxCurve x t₀ s) s t).comp
      (normalizedFlowDifferential x t₀ s) = normalizedFlowDifferential x t₀ t := by
  have hst : t ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ s) s := by
    rwa [normalizedMaxDomain_rebase hs]
  have hd := (hasFDerivAt_normalizedMaxCurve_initial hst).comp x
    (hasFDerivAt_normalizedMaxCurve_initial hs)
  have heq : (fun y => normalizedMaxCurve (normalizedMaxCurve y t₀ s) s t)
      =ᶠ[𝓝 x] (fun y => normalizedMaxCurve y t₀ t) := by
    have hc (u : ℝ) : ContinuousAt (fun y : NormalizedState => (y, u)) x := by fun_prop
    filter_upwards [(hc s).eventually ((isOpen_normalizedFlowDomain t₀).mem_nhds hs),
      (hc t).eventually ((isOpen_normalizedFlowDomain t₀).mem_nhds ht)] with y hys hyt
    exact normalizedMaxCurve_rebase hys hyt
  exact (hd.congr_of_eventuallyEq heq.symm).unique (hasFDerivAt_normalizedMaxCurve_initial ht)
