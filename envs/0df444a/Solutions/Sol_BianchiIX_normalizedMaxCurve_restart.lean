-- Prove2me | solution 1 for BianchiIX.normalizedMaxCurve_restart
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:20:08.728128+00:00
-- url     : https://prove2.me/submissions/2d4e1cc9-5e75-4298-ae66-f7edbac7a8d4

import Definitions.Def_BianchiIX_Dynamics_FlowComposition
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
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_retime {x : NormalizedState} {t₀ t₁ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₁) :
    normalizedMaxCurve x t₁ t = normalizedMaxCurve x t₀ (t + t₀ - t₁) :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).retime t₁)
    (mem_normalizedMaxDomain_retime.mp ht)

private theorem BianchiIX.normalizedMaxCurve_rebase {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (normalizedMaxCurve x t₀ s) s t = normalizedMaxCurve x t₀ t :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).rebase hs) ht

/-- A local restart proves membership in the original maximal domain as well as the flow identity. -/
theorem solution {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀)
    (ht : t - s ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ s) 0) :
    t ∈ normalizedMaxDomain x t₀ ∧
      normalizedMaxCurve x t₀ t = normalizedMaxCurve (normalizedMaxCurve x t₀ s) 0 (t - s) := by
  have ht' : t ∈ normalizedMaxDomain (normalizedMaxCurve x t₀ s) s :=
    (mem_normalizedMaxDomain_retime (t₀ := (0 : ℝ))).mpr (by simpa using ht)
  have hmem : t ∈ normalizedMaxDomain x t₀ := by rwa [normalizedMaxDomain_rebase hs] at ht'
  refine ⟨hmem, (normalizedMaxCurve_rebase hs hmem).symm.trans ?_⟩
  simpa using (normalizedMaxCurve_retime (t₀ := (0 : ℝ)) ht')
