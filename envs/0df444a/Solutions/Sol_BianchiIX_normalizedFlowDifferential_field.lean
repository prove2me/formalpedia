-- Prove2me | solution 1 for BianchiIX.normalizedFlowDifferential_field
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:26:04.578207+00:00
-- url     : https://prove2.me/submissions/237f4d49-0e03-47b0-8ed8-b7edcd439f60

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
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
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedFlowDifferential x t₀ t (normalizedField x) =
      normalizedField (normalizedMaxCurve x t₀ t) := by
  have hstart : HasDerivAt (fun u => normalizedMaxCurve x t₀ (t₀ + u)) (normalizedField x) 0 := by
    have hd := hasDerivAt_normalizedMaxCurve (x₀ := x) (t₀ := t₀) (t := t₀ + 0)
      (by simpa using initial_mem_normalizedMaxDomain x t₀)
    convert! hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add t₀) using 1
    simp [normalizedMaxCurve_initial]
  have hend : HasDerivAt (fun u => normalizedMaxCurve x t₀ (t + u))
      (normalizedField (normalizedMaxCurve x t₀ t)) 0 := by
    have hd := hasDerivAt_normalizedMaxCurve (x₀ := x) (t₀ := t₀) (t := t + 0) (by simpa using ht)
    convert! hd.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add t) using 1
    simp
  have hp : HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t)
      (normalizedMaxCurve x t₀ (t₀ + 0)) := by
    simpa only [add_zero, normalizedMaxCurve_initial] using hasFDerivAt_normalizedMaxCurve_initial ht
  have hcomp := hp.comp_hasDerivAt 0
    (show HasDerivAt (fun u => normalizedMaxCurve x t₀ (t₀ + u)) (normalizedField x) 0 from hstart)
  have heq : (fun u => normalizedMaxCurve x t₀ (t + u)) =ᶠ[𝓝 0]
      (fun u => normalizedMaxCurve (normalizedMaxCurve x t₀ (t₀ + u)) t₀ t) := by
    have hc (s : ℝ) : ContinuousAt (fun u : ℝ => s + u) 0 := by fun_prop
    have hs := (hc t₀).eventually ((isOpen_normalizedMaxDomain x t₀).mem_nhds
      (by simpa using initial_mem_normalizedMaxDomain x t₀))
    have he := (hc t).eventually ((isOpen_normalizedMaxDomain x t₀).mem_nhds (by simpa using ht))
    filter_upwards [hs, he] with u hu htu
    exact (normalizedMaxCurve_shift hu htu).symm
  exact (hcomp.congr_of_eventuallyEq heq).unique hend
