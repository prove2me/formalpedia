-- Prove2me | solution 1 for BianchiIX.hasFDerivAt_normalizedMaxCurve
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:27:23.115567+00:00
-- url     : https://prove2.me/submissions/482c7bff-df9a-4a8a-a62d-4b0675bca45d

import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Theorems.Thm_BianchiIX_normalizedMaxCurve_fderiv_initial
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
open Set


theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
      ((normalizedFlowDifferential x t₀ t).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField (normalizedMaxCurve x t₀ t))))
      (x, t) := by
  have H := ((normalizedMaxCurve_regular ht).2.differentiableAt (by norm_num)).hasFDerivAt
  have hright := (H.comp t (hasFDerivAt_prodMk_right x t)).unique
    (hasDerivAt_normalizedMaxCurve ht).hasFDerivAt
  have heq : ContinuousLinearMap.toSpanSingleton ℝ (normalizedField (normalizedMaxCurve x t₀ t)) =
      (ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField (normalizedMaxCurve x t₀ t)) := by
    ext u
    rfl
  rw [heq] at hright
  rw [← normalizedMaxCurve_fderiv_initial ht, ← hright, ContinuousLinearMap.coprod_comp_inl_inr]
  exact H
