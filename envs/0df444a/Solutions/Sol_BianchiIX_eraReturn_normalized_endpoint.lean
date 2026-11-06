-- Prove2me | solution 1 for BianchiIX.eraReturn_normalized_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:35:11.511998+00:00
-- url     : https://prove2.me/submissions/86450a5b-e2c5-414c-9032-4f37280f99db

import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

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

private theorem BianchiIX.fromProjectiveState_reflection (y : ProjectiveState) :
    fromProjectiveState (projectiveReflection y) = axisSwap (fromProjectiveState y) := by
  simp only [fromProjectiveState, projectiveReflection_denom]
  ext i
  fin_cases i <;> dsimp [projectiveReflection, axisSwap]
  all_goals ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_shears (x : NormalizedState) :
    normalizedShears (axisCycle x) = ![normalizedShears x 1, normalizedShears x 2, normalizedShears x 0] := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisCycle] <;> ring_nf <;> norm_num [hs] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_shears (x : NormalizedState) :
    normalizedShears (axisSwap x) = ![normalizedShears x 0, normalizedShears x 2, normalizedShears x 1] := by
  ext i
  fin_cases i <;> dsimp [normalizedShears, axisSwap] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisOrder_bijective : ∀ i, Function.Bijective (axisOrder i) := by decide

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_apply (i : Fin 6) (x : NormalizedState) :
    (axisFrame i).map x =
      ![x, axisCycle x, axisCycle (axisCycle x), axisSwap x,
        axisSwap (axisCycle x), axisSwap (axisCycle (axisCycle x))] i := by
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_walls (i : Fin 6) (x : NormalizedState) :
    normalizedWalls ((axisFrame i).map x) = fun j => normalizedWalls x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_shears (i : Fin 6) (x : NormalizedState) :
    normalizedShears ((axisFrame i).map x) = fun j => normalizedShears x (axisOrder i j) := by
  rw [axisFrame_apply]
  fin_cases i
  · ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle x) = _
    rw [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisCycle (axisCycle x)) = _
    simp only [axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap x) = _
    rw [axisSwap_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle x)) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl
  · change normalizedShears (axisSwap (axisCycle (axisCycle x))) = _
    simp only [axisSwap_shears, axisCycle_shears]
    ext j
    fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedState_ext_shears_walls {x y : NormalizedState}
    (hs : normalizedShears x = normalizedShears y) (hw : normalizedWalls x = normalizedWalls y) : x = y := by
  have h₀ := congrFun hs 0
  have h₁ := congrFun hs 1
  change -2 * x 0 = -2 * y 0 at h₀
  change x 0 - Real.sqrt 3 * x 1 = y 0 - Real.sqrt 3 * y 1 at h₁
  have hx₀ : x 0 = y 0 := by linarith
  have hx₁ : x 1 = y 1 := mul_left_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 3))
    (by linarith : Real.sqrt 3 * x 1 = Real.sqrt 3 * y 1)
  ext i
  fin_cases i
  · exact hx₀
  · exact hx₁
  · exact congrFun hw 0
  · exact congrFun hw 1
  · exact congrFun hw 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_comp (i j : Fin 6) :
    ∃ k : Fin 6, ∀ x : NormalizedState,
      (axisFrame i).map ((axisFrame j).map x) = (axisFrame k).map x := by
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective (axisOrder i) (axisOrder_bijective i)
  let τ : Equiv.Perm (Fin 3) := Equiv.ofBijective (axisOrder j) (axisOrder_bijective j)
  obtain ⟨k, hk⟩ := axisOrder_covers (σ.trans τ)
  refine ⟨k, fun x => normalizedState_ext_shears_walls ?_ ?_⟩
  · ext l
    simp only [axisFrame_shears, hk]
    rfl
  · ext l
    simp only [axisFrame_walls, hk]
    rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreRadiusReturnValid_denom_pos {Y : CoreAngleState} (H : coreRadiusReturnValid Y) :
    0 < projectiveStateDenom (coreRadiusEntry Y) := by
  have hzero := (H.2.1 0 ⟨le_rfl, H.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreRadiusEntry Y) - 1) at hzero
  by_contra! hn
  have HD := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, HD]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreReflection_normalized_endpoint {Y : CoreAngleState}
    (hcore : coreRadiusReturnValid Y) (hT : 0 < coreReflectionTime Y)
    (hentry : coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) =
      projectiveReflection (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))) :
    fromProjectiveState (coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y)) =
      axisSwap (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (coreReflectionTime Y)) := by
  let x := fromProjectiveState (coreRadiusEntry Y)
  let T := coreReflectionTime Y
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos hcore).ne'
  have hd : T ∈ normalizedMaxDomain x 0 := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.le
  have hA : 1 + normalizedMaxCurve x 0 T 0 ≠ 0 := by
    intro hz
    have H := congrArg (fun y : ProjectiveState => y 2) hentry
    change 1 = projectiveCoord (normalizedMaxCurve x 0 T 0) (normalizedMaxCurve x 0 T 4) at H
    simp only [projectiveCoord, hz, div_zero] at H
    norm_num at H
  rw [hentry, fromProjectiveState_reflection]
  exact congrArg axisSwap (fromProjectiveState_toProjectiveState hA ((normalizedMaxCurve_constraint hd).trans hc))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.unit_active_wall_clock_ne_zero {x : NormalizedState} (hv : toProjectiveState x 2 = 1) :
    1 + x 0 ≠ 0 := by
  intro hzero
  change projectiveCoord (x 0) (x 3) = 1 at hv
  simp only [projectiveCoord, hzero, div_zero] at hv
  norm_num at hv

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreReturn_normalized_endpoint {Y : CoreAngleState} (H : coreRadiusReturnValid Y)
    (hchart : coreTailEntry (coreReturnState coreRadiusReturnTime Y) =
      projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreRadiusReturnTime Y)) :
    fromProjectiveState (coreTailEntry (coreReturnState coreRadiusReturnTime Y)) =
      normalizedMaxCurve (fromProjectiveState (coreRadiusEntry Y)) 0 (coreRadiusReturnTime Y) := by
  have hA := (H.2.1 (coreRadiusReturnTime Y) ⟨H.1.1.1.le, le_rfl⟩).2
  rw [hchart]
  exact fromProjectiveState_toProjectiveState hA.ne'
    ((normalizedMaxCurve_constraint H.1.1.2.1).trans
      (fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos H).ne'))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.corePrefixFrame_succ (m : ℕ) (x : NormalizedState) :
    (axisFrame (corePrefixFrame (m + 1))).map x = axisSwap ((axisFrame (corePrefixFrame m)).map x) :=
  ((axisFrame_comp 3 (corePrefixFrame m)).choose_spec x).symm

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.corePrefixTime_succ (m : ℕ) (X : CoreAngleState) :
    corePrefixTime (m + 1) X = coreReflectionTime ((coreReflectionState coreRadiusReturnTime)^[m] X) +
      corePrefixTime m X := by
  rw [corePrefixTime, Finset.sum_range_succ]
  exact add_comm _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.corePrefix_normalized_endpoint {m : ℕ} {X : CoreAngleState}
    (Hvalid : ∀ j ≤ m, coreRadiusReturnValid ((coreReflectionState coreRadiusReturnTime)^[j] X))
    (Hconn : ∀ j < m,
      let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
      0 < coreReflectionTime Y ∧
        coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) = projectiveReflection
          (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y))) :
    0 ≤ corePrefixTime m X ∧
      fromProjectiveState (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[m] X)) =
        (axisFrame (corePrefixFrame m)).map
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry X)) 0 (corePrefixTime m X)) := by
  let x := fromProjectiveState (coreRadiusEntry X)
  have hc : stateConstraint x = 1 :=
    fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos (Hvalid 0 (Nat.zero_le _))).ne'
  induction m with
  | zero =>
    simp only [corePrefixTime, Finset.range_zero, Finset.sum_empty, Function.iterate_zero_apply,
      corePrefixFrame, normalizedMaxCurve_initial]
    exact ⟨le_rfl, rfl⟩
  | succ m ih =>
    obtain ⟨hT, hend⟩ := ih (fun j hj => Hvalid j (by omega)) (fun j hj => Hconn j (by omega))
    obtain ⟨ht, hlocal⟩ := Hconn m (by omega)
    have hcT : stateConstraint (normalizedMaxCurve x 0 (corePrefixTime m X)) = 1 :=
      (normalizedMaxCurve_forward_of_constraint hc hT).2.1
    have hshift := normalizedMaxCurve_shift (t₀ := (0 : ℝ))
      (t := coreReflectionTime ((coreReflectionState coreRadiusReturnTime)^[m] X))
      (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 (add_nonneg ht.le hT))
    simp only [zero_add] at hshift
    refine ⟨by rw [corePrefixTime_succ]; exact add_nonneg ht.le hT, ?_⟩
    rw [Function.iterate_succ_apply',
      coreReflection_normalized_endpoint (Hvalid m (by omega)) ht hlocal, hend,
      (axisFrame (corePrefixFrame m)).maxCurve
        (normalizedMaxDomain_contains_Ici_of_constraint hcT 0 ht.le),
      hshift, corePrefixTime_succ, corePrefixFrame_succ]

end
end

private theorem BianchiIX.eraReturnFrame_apply (m : ℕ) (x : NormalizedState) :
    (axisFrame (eraReturnFrame m)).map x = axisCycle ((axisFrame (corePrefixFrame m)).map x) :=
  ((axisFrame_comp 1 (corePrefixFrame m)).choose_spec x).symm


/-- The local event identities compose in normalized time, without requiring one projective chart along the entire era. -/
theorem solution {η : ℝ} {J m : ℕ} {X : CoreAngleState}
    (Hvalid : ∀ j ≤ m, coreRadiusReturnValid ((coreReflectionState coreRadiusReturnTime)^[j] X))
    (Hconn : ∀ j < m,
      let Y := (coreReflectionState coreRadiusReturnTime)^[j] X
      0 < coreReflectionTime Y ∧
        coreRadiusEntry (coreReflectionState coreRadiusReturnTime Y) = projectiveReflection
          (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y)))
    (hchart : coreTailEntry (eraCoreExit m X) = projectiveOriginalFlow
      (coreRadiusEntry ((coreReflectionState coreRadiusReturnTime)^[m] X)) 0
      (coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X)))
    (hT : 0 < terminalNaturalTime η J (eraCoreExit m X))
    (hactual : toProjectiveState (normalizedMaxCurve
      (axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X)))) 0
      (terminalNaturalTime η J (eraCoreExit m X))) = terminalNaturalState η J (eraCoreExit m X))
    (hunit : terminalNaturalState η J (eraCoreExit m X) 2 = 1) :
    0 < eraReturnTime η J m X ∧
      eraReturnTime η J m X ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry X)) 0 ∧
      fromProjectiveState (terminalNaturalState η J (eraCoreExit m X)) =
        (axisFrame (eraReturnFrame m)).map
          (normalizedMaxCurve (fromProjectiveState (coreRadiusEntry X)) 0 (eraReturnTime η J m X)) := by
  let x := fromProjectiveState (coreRadiusEntry X)
  let S := coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X) + corePrefixTime m X
  let T := terminalNaturalTime η J (eraCoreExit m X)
  have hc : stateConstraint x = 1 :=
    fromProjectiveState_constraint (coreRadiusReturnValid_denom_pos (Hvalid 0 (Nat.zero_le _))).ne'
  obtain ⟨hp, hprefix⟩ := corePrefix_normalized_endpoint Hvalid Hconn
  have hdown := (Hvalid m le_rfl).1.1.1
  have hS : 0 < S := add_pos_of_pos_of_nonneg hdown hp
  have hcP : stateConstraint (normalizedMaxCurve x 0 (corePrefixTime m X)) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc hp).2.1
  have hshift := normalizedMaxCurve_shift (t₀ := (0 : ℝ))
    (t := coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X))
    (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hp)
    (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hS.le)
  simp only [zero_add] at hshift
  have hexit : fromProjectiveState (coreTailEntry (eraCoreExit m X)) =
      (axisFrame (corePrefixFrame m)).map (normalizedMaxCurve x 0 S) := by
    change fromProjectiveState (coreTailEntry
      (coreReturnState coreRadiusReturnTime ((coreReflectionState coreRadiusReturnTime)^[m] X))) = _
    rw [coreReturn_normalized_endpoint (Hvalid m le_rfl) hchart, hprefix,
      (axisFrame (corePrefixFrame m)).maxCurve
        (normalizedMaxDomain_contains_Ici_of_constraint hcP 0 hdown.le), hshift]
  have hstart : axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X))) =
      (axisFrame (eraReturnFrame m)).map (normalizedMaxCurve x 0 S) := by
    rw [hexit, eraReturnFrame_apply]
  have hcS : stateConstraint (normalizedMaxCurve x 0 S) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc hS.le).2.1
  have hsum : 0 < eraReturnTime η J m X := add_pos hT hS
  have hflow : normalizedMaxCurve
      (axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X)))) 0 T =
        (axisFrame (eraReturnFrame m)).map (normalizedMaxCurve x 0 (eraReturnTime η J m X)) := by
    rw [hstart, (axisFrame (eraReturnFrame m)).maxCurve
      (normalizedMaxDomain_contains_Ici_of_constraint hcS 0 hT.le)]
    have H := normalizedMaxCurve_shift (t₀ := (0 : ℝ)) (t := T)
      (by simpa only [zero_add] using normalizedMaxDomain_contains_Ici_of_constraint hc 0 hS.le)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hsum.le)
    simpa only [zero_add, eraReturnTime, S, T] using congrArg (axisFrame (eraReturnFrame m)).map H
  have hcend : stateConstraint (normalizedMaxCurve
      (axisCycle (fromProjectiveState (coreTailEntry (eraCoreExit m X)))) 0 T) = 1 := by
    rw [hflow, (axisFrame (eraReturnFrame m)).constraint]
    exact (normalizedMaxCurve_forward_of_constraint hc hsum.le).2.1
  refine ⟨hsum, normalizedMaxDomain_contains_Ici_of_constraint hc 0 hsum.le, ?_⟩
  rw [← hactual, fromProjectiveState_toProjectiveState
    (unit_active_wall_clock_ne_zero (by rw [hactual]; exact hunit)) hcend]
  exact hflow
