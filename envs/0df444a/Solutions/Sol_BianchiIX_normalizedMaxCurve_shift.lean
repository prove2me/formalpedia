-- Prove2me | solution 1 for BianchiIX.normalizedMaxCurve_shift
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:20:35.469832+00:00
-- url     : https://prove2.me/submissions/0bb41ec5-b8e7-48e2-a696-458ad8510390

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowComposition
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Theorems.Thm_BianchiIX_mem_normalizedMaxDomain_retime
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
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_retime {x : NormalizedState} {t₀ t₁ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₁) :
    normalizedMaxCurve x t₁ t = normalizedMaxCurve x t₀ (t + t₀ - t₁) :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).retime t₁)
    (mem_normalizedMaxDomain_retime.mp ht)

end
end

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

theorem solution {x : NormalizedState} {t₀ t u : ℝ}
    (hu : t₀ + u ∈ normalizedMaxDomain x t₀) (ht : t + u ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (normalizedMaxCurve x t₀ (t₀ + u)) t₀ t = normalizedMaxCurve x t₀ (t + u) := by
  have hd : t + u ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ (t₀ + u)) (t₀ + u) := by
    rwa [normalizedMaxDomain_rebase hu]
  have hd' : t ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ (t₀ + u)) t₀ := by
    apply (mem_normalizedMaxDomain_retime (t₀ := t₀ + u)).mpr
    convert! hd using 1
    ring
  have H := normalizedMaxCurve_retime (t₀ := t₀ + u) hd'
  rw [show t + (t₀ + u) - t₀ = t + u by ring] at H
  exact H.trans (normalizedMaxCurve_rebase hu ht)
