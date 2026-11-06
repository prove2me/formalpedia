-- Prove2me | solution 1 for BianchiIX.compactConnection_actual_passage
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:01:17.237293+00:00
-- url     : https://prove2.me/submissions/731f5353-3793-4dc6-b1c1-c8869a40708f

import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_projectiveOriginalFlow_reflection
import Theorems.Thm_BianchiIX_projectiveOriginalFlow_restart
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.projectiveReflection_denom (y : ProjectiveState) :
    projectiveStateDenom (projectiveReflection y) = projectiveStateDenom y := by
  dsimp [projectiveStateDenom, projectiveDenom, projectiveReflection, curvature]
  ring

end
end

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

/-- The two passages give the first new-wall arrival on one exact Einstein orbit. -/
theorem solution {η : ℝ} {Y : CoreAngleState}
    (htail : coreTailValid η Y) (hD : 0 < projectiveStateDenom (compactConnectionEntry η Y))
    (hreturn : entranceReturnValid (compactConnectionEntry η Y)) :
    compactConnectionState η Y = projectiveReflection
      (projectiveOriginalFlow (coreTailEntry Y) 0 (compactConnectionTime η Y)) ∧
      IsLeast {t : ℝ | 0 < t ∧ projectiveReflection
        (projectiveOriginalFlow (coreTailEntry Y) 0 t) 2 = 1} (compactConnectionTime η Y) := by
  let y := compactConnectionEntry η Y
  let S := coreTailTime η Y
  let T := entranceReturnTime y
  have hS : 0 < S := htail.1.1.1
  have hT : 0 < T := hreturn.1.1.1
  have hDi := coreTailValid_denom_pos htail
  have hDs : 0 < projectiveStateDenom (coreTailState η Y) := by
    rw [← projectiveReflection_denom]
    exact hD
  have hbridge (t : ℝ) (ht : 0 ≤ t) : projectiveOriginalFlow y 0 t =
      projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (t + S)) := by
    have hdom := normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hDs.ne') 0 ht
    have href := projectiveOriginalFlow_reflection hdom
    have hre := projectiveOriginalFlow_restart hDi hS.le ht (htail.2.1 S ⟨hS.le, le_rfl⟩).2
    exact href.trans (congrArg projectiveReflection hre)
  have heq : compactConnectionState η Y = projectiveReflection
      (projectiveOriginalFlow (coreTailEntry Y) 0 (T + S)) := hbridge T hT.le
  refine ⟨heq, ⟨add_pos hT hS, ?_⟩, ?_⟩
  · change projectiveReflection (projectiveOriginalFlow (coreTailEntry Y) 0 (T + S)) 2 = 1
    rw [← heq]
    exact hreturn.1.1.2.2
  · intro t ht
    by_cases hts : t ≤ S
    · have hsmall := htail.2.2.2.2 t ⟨ht.1.le, hts⟩
      change |projectiveOriginalFlow (coreTailEntry Y) 0 t 3| < 1 / 2 at hsmall
      have hh : projectiveOriginalFlow (coreTailEntry Y) 0 t 3 = 1 := ht.2
      rw [hh, abs_one] at hsmall
      norm_num at hsmall
    · have hst : 0 < t - S := sub_pos.mpr (lt_of_not_ge hts)
      have hhit : projectiveOriginalFlow y 0 (t - S) 2 = 1 := by
        rw [hbridge (t - S) hst.le, sub_add_cancel]
        exact ht.2
      have hle := hreturn.1.2 ⟨hst,
        normalizedMaxDomain_contains_Ici_of_constraint (fromProjectiveState_constraint hD.ne') 0 hst.le, hhit⟩
      change T ≤ t - S at hle
      change T + S ≤ t
      linarith
