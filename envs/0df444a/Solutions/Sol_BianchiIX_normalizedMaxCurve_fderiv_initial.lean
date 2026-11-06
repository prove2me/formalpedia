-- Prove2me | solution 1 for BianchiIX.normalizedMaxCurve_fderiv_initial
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:25:58.669246+00:00
-- url     : https://prove2.me/submissions/1c7c1968-4724-4085-8cb3-0363f24c05ec

import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
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

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

theorem solution {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    (fderiv ℝ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t)).comp
      (ContinuousLinearMap.inl ℝ NormalizedState ℝ) = normalizedFlowDifferential x t₀ t := by
  have H := ((normalizedMaxCurve_regular ht).2.differentiableAt (by norm_num)).hasFDerivAt
  have hleft : HasFDerivAt (fun y => normalizedMaxCurve y t₀ t)
      ((fderiv ℝ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t)).comp
        (ContinuousLinearMap.inl ℝ NormalizedState ℝ)) x := by
    convert! H.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t) using 1
  exact hleft.unique (hasFDerivAt_normalizedMaxCurve_initial ht)
