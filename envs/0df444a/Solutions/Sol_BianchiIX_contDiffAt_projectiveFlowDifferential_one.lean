-- Prove2me | solution 1 for BianchiIX.contDiffAt_projectiveFlowDifferential_one
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:13:52.695144+00:00
-- url     : https://prove2.me/submissions/58eae202-0a59-466d-997b-207d98e126f8

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_fderiv_initial
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
open BianchiIX
open Set

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
open Set Filter Metric
open scoped Topology ContDiff

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_smooth {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ ∞ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  contDiffAt_infty.mpr (fun n => contDiffAt_normalizedMaxCurve_nat n ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffOn_normalizedMaxCurve_two (t₀ : ℝ) :
    ContDiffOn ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
      (normalizedFlowDomain t₀) :=
  fun _ hz => (contDiffAt_normalizedMaxCurve_two hz).contDiffWithinAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffOn_normalizedFlowDifferential_one (t₀ : ℝ) :
    ContDiffOn ℝ 1 (fun z : NormalizedState × ℝ => normalizedFlowDifferential z.1 t₀ z.2)
      (normalizedFlowDomain t₀) := by
  have hc := (contDiffOn_normalizedMaxCurve_two t₀).fderiv_of_isOpen
    (isOpen_normalizedFlowDomain t₀) (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  exact (hc.clm_comp (contDiffOn_const (c := ContinuousLinearMap.inl ℝ NormalizedState ℝ))).congr
    (fun z hz => (normalizedMaxCurve_fderiv_initial hz).symm)

end
end

theorem solution {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    ContDiffAt ℝ 1 (fun z : ProjectiveState × ℝ => projectiveFlowDifferential z.1 t₀ z.2) (y, t) := by
  have hparam : ContDiffAt ℝ 1 (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 1 hD.ne').comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hN : ContDiffAt ℝ 1
      (fun z : ProjectiveState × ℝ => normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2) (y, t) := by
    have H := ((contDiffAt_normalizedMaxCurve_two ht).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp (y, t) hparam
    simpa only [Function.comp_def] using H
  have hJ := ((contDiffOn_normalizedFlowDifferential_one t₀).contDiffAt
    ((isOpen_normalizedFlowDomain t₀).mem_nhds ht)).comp (y, t) hparam
  have hto := ((contDiffAt_toProjectiveState 2 hA.ne').fderiv_right
    (m := 1) (by norm_num)).comp (y, t) hN
  have hfrom := ((contDiffAt_fromProjectiveState 2 hD.ne').fderiv_right
    (m := 1) (by norm_num)).comp (y, t) contDiffAt_fst
  exact hto.clm_comp (hJ.clm_comp hfrom)
