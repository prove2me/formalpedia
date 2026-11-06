-- Prove2me | solution 1 for BianchiIX.hasDerivAt_normalizedFlowDifferential
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:28:15.039275+00:00
-- url     : https://prove2.me/submissions/1e29019f-6437-421e-9923-08fc5de2e0d6

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Theorems.Thm_BianchiIX_exists_normalizedMaxCurve_local_derivative
import Theorems.Thm_BianchiIX_normalizedFlowDifferential_rebase
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
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
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

/-- The time equation for the genuine initial-state derivative on the whole maximal interval. -/
theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasDerivAt (fun u => normalizedFlowDifferential x t₀ u)
      ((normalizedDifferential (normalizedMaxCurve x t₀ t)).comp
        (normalizedFlowDifferential x t₀ t)) t := by
  let z := normalizedMaxCurve x t₀ t
  obtain ⟨r, hr, ε, hε, J, _, _, hJ⟩ := exists_normalizedMaxCurve_local_derivative z t
  have hz : z ∈ ball z r := mem_ball_self hr
  have htt : t ∈ Ioo (t - ε) (t + ε) := by constructor <;> linarith
  have hd := ((hJ z hz).2.2 t htt).2.clm_comp
    (hasDerivAt_const t (normalizedFlowDifferential x t₀ t))
  have heq : (fun u => (J (z, u)).comp (normalizedFlowDifferential x t₀ t))
      =ᶠ[𝓝 t] (fun u => normalizedFlowDifferential x t₀ u) := by
    filter_upwards [Ioo_mem_nhds htt.1 htt.2,
      (isOpen_normalizedMaxDomain x t₀).mem_nhds ht] with u hu hdom
    have hJu : J (z, u) = normalizedFlowDifferential z t u :=
      ((hJ z hz).2.2 u hu).1.unique
        (hasFDerivAt_normalizedMaxCurve_initial ((hJ z hz).1 hu))
    rw [hJu]
    exact normalizedFlowDifferential_rebase ht hdom
  simpa only [(hJ z hz).2.1, normalizedMaxCurve_initial, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.comp_zero, add_zero] using hd.congr_of_eventuallyEq heq.symm
