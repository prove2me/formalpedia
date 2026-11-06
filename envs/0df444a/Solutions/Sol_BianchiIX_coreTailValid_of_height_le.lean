-- Prove2me | solution 1 for BianchiIX.coreTailValid_of_height_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:06:35.777354+00:00
-- url     : https://prove2.me/submissions/1bb22fa9-0589-475c-a302-763948df1a78

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailValid_denom_pos {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    0 < projectiveStateDenom (coreTailEntry Y) := by
  have hzero := (hvalid.2.1 0 ⟨le_rfl, hvalid.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at hzero
  by_contra! hn
  have H := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, H]

end
end

/-- Every intermediate height is reached on the same strictly decreasing finite tail. -/
theorem solution {h₀ h : ℝ} {Y : CoreAngleState}
    (HV : coreTailValid h₀ Y) (hlo : h₀ ≤ h) (hhi : h < 1) :
    coreTailValid h Y ∧ coreTailTime h Y ≤ coreTailTime h₀ Y := by
  let x := fromProjectiveState (coreTailEntry Y)
  let T := coreTailTime h₀ Y
  let V := fun t => projectiveActiveWall (normalizedMaxCurve x 0 t)
  have hT : 0 < T := HV.1.1.1
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt V (normalizedEventRate projectiveActiveWall x 0 t) t :=
    ((contDiffAt_projectiveActiveWall 1 (HV.2.1 t ht).2.ne').differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve (HV.2.1 t ht).1)
  have hmono : StrictAntiOn V (Icc 0 T) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (HasDerivAt.continuousOn hderiv)
    intro t ht
    rw [(hderiv t (interior_subset ht)).deriv]
    exact HV.2.2.2.1 t (interior_subset ht)
  have hV0 : V 0 = 1 := by
    dsimp only [V, x, projectiveActiveWall]
    rw [normalizedMaxCurve_initial, toProjectiveState_fromProjectiveState (coreTailValid_denom_pos HV).ne']
    rfl
  have hVT : V T = h₀ := HV.1.1.2.2
  obtain ⟨t, ht, hhit⟩ := intermediate_value_Icc' hT.le (HasDerivAt.continuousOn hderiv)
    (show h ∈ Icc (V T) (V 0) by rw [hVT, hV0]; exact ⟨hlo, hhi.le⟩)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
    intro heq
    rw [← heq, hV0] at hhit
    linarith only [hhit, hhi])
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hbefore (r : ℝ) (hr : r ∈ Ico 0 t) : h < V r := by
    rw [← hhit]
    exact hmono (hsub ⟨hr.1, hr.2.le⟩) ht hr.2
  have hfirst : IsLeast {r | 0 < r ∧ r ∈ normalizedMaxDomain x 0 ∧ V r = h} t := by
    refine ⟨⟨htpos, (HV.2.1 t ht).1, hhit⟩, ?_⟩
    intro r hr
    by_contra hn
    have H := hbefore r ⟨hr.1.le, lt_of_not_ge hn⟩
    rw [hr.2.2] at H
    exact lt_irrefl _ H
  have htime : coreTailTime h Y = t := hfirst.csInf_eq
  refine ⟨?_, by rw [htime]; exact ht.2⟩
  dsimp only [coreTailValid]
  rw [htime]
  exact ⟨hfirst, (fun r hr => HV.2.1 r (hsub hr)), hbefore,
    (fun r hr => HV.2.2.2.1 r (hsub hr)), fun r hr => HV.2.2.2.2 r (hsub hr)⟩
