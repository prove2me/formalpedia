-- Prove2me | solution 1 for BianchiIX.exists_late_physical_core
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:12:31.405676+00:00
-- url     : https://prove2.me/submissions/4284e218-40bd-4a25-b1fe-d3d5090f7bc6

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_exists_fixedWall_physical_core
import Theorems.Thm_BianchiIX_exists_late_fixedWall_entrance
import Theorems.Thm_BianchiIX_normalizedMaxCurve_restart
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_positive_walls_invariant
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
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

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.axisFrame_wallValue (a : Fin 6) (x : NormalizedState) (i : Fin 3) :
    wallValue i ((axisFrame a).map x) = wallValue (axisOrder a i) x := by
  have heq (y : NormalizedState) (j : Fin 3) : normalizedWalls y j = wallValue j y := by
    fin_cases j <;> rfl
  simpa only [heq] using congrFun (axisFrame_walls a x) i

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalizedWallProductsBound.axisFrame {x : NormalizedState} {Δ : ℝ}
    (H : normalizedWallProductsBound Δ x) (a : Fin 6) :
    normalizedWallProductsBound Δ ((axisFrame a).map x) := by
  fin_cases a <;>
    simpa [normalizedWallProductsBound, axisFrame_apply, axisCycle, axisSwap,
      mul_comm, mul_left_comm, mul_assoc, and_assoc, and_comm, and_left_comm] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_wallRate {x : NormalizedState} (hp : positiveWalls x) (a : Fin 6) (i : Fin 3) :
    wallRate i ((axisFrame a).map x) = wallRate (axisOrder a i) x := by
  have hfield (j : Fin 3) (y : NormalizedState) :
      wallValue j (normalizedField y) = wallRate j y * wallValue j y := by
    fin_cases j <;> rfl
  have hpos (j : Fin 3) : 0 < wallValue j x := by
    fin_cases j
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2
  have H := congrArg (wallValue i) ((axisFrame a).field x)
  rw [hfield, axisFrame_wallValue, axisFrame_wallValue, hfield] at H
  exact mul_right_cancel₀ (hpos (axisOrder a i)).ne' H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_axisFrame_first_wall (i : Fin 3) : ∃ a : Fin 6, axisOrder a 0 = i := by
  fin_cases i
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedWallProductsBound.forward {x : NormalizedState} {Δ s : ℝ}
    (hc : stateConstraint x = 1)
    (H : ∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u))
    (hs : 0 ≤ s) :
    ∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ
      (normalizedMaxCurve (normalizedMaxCurve x 0 s) 0 u) := by
  intro u hu
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs
  have hcs : stateConstraint (normalizedMaxCurve x 0 s) = 1 :=
    (normalizedMaxCurve_constraint hdom).trans hc
  have heq := (normalizedMaxCurve_restart (t := s + u) hdom (by
    simpa only [add_sub_cancel_left] using normalizedMaxDomain_contains_Ici_of_constraint hcs 0 hu)).2
  simp only [add_sub_cancel_left] at heq
  rw [← heq]
  exact H _ (add_nonneg hs hu)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedEuclideanDistance_nonneg (x y : NormalizedState) :
    0 ≤ normalizedEuclideanDistance x y := dist_nonneg

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedEuclideanDistance_sq (x y : NormalizedState) :
    normalizedEuclideanDistance x y ^ 2 = ∑ i, (x i - y i) ^ 2 := by
  simp [normalizedEuclideanDistance, EuclideanSpace.dist_sq_eq, Real.dist_eq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_euclideanDistance (x y : NormalizedState) :
    normalizedEuclideanDistance (axisCycle x) (axisCycle y) = normalizedEuclideanDistance x y := by
  apply (sq_eq_sq₀ (normalizedEuclideanDistance_nonneg _ _)
    (normalizedEuclideanDistance_nonneg _ _)).mp
  rw [normalizedEuclideanDistance_sq, normalizedEuclideanDistance_sq]
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp [Fin.sum_univ_succ, axisCycle]
  ring_nf
  rw [hs]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_euclideanDistance (x y : NormalizedState) :
    normalizedEuclideanDistance (axisSwap x) (axisSwap y) = normalizedEuclideanDistance x y := by
  apply (sq_eq_sq₀ (normalizedEuclideanDistance_nonneg _ _)
    (normalizedEuclideanDistance_nonneg _ _)).mp
  rw [normalizedEuclideanDistance_sq, normalizedEuclideanDistance_sq]
  simp [Fin.sum_univ_succ, axisSwap]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_euclideanDistance (i : Fin 6) (x y : NormalizedState) :
    normalizedEuclideanDistance ((axisFrame i).map x) ((axisFrame i).map y) =
      normalizedEuclideanDistance x y := by
  rw [axisFrame_apply, axisFrame_apply]
  fin_cases i <;> simp [axisCycle_euclideanDistance, axisSwap_euclideanDistance]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_taubPoint (i : Fin 3) : axisCycle (taubPoint i) = taubPoint (i + 2) := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i
  · change axisCycle ![-1, 0, 0, 0, 0] = ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisCycle] <;> ring
  · change axisCycle ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0] = ![-1, 0, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisCycle] <;> ring_nf
    norm_num [hs]
  · change axisCycle ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0] = ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisCycle] <;> ring_nf
    norm_num [hs]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisSwap_taubPoint (i : Fin 3) : axisSwap (taubPoint i) = taubPoint (-i) := by
  fin_cases i
  · change axisSwap ![-1, 0, 0, 0, 0] = ![-1, 0, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisSwap]
    ring
  · change axisSwap ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0] = ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisSwap]
    ring
  · change axisSwap ![1 / 2, Real.sqrt 3 / 2, 0, 0, 0] = ![1 / 2, -Real.sqrt 3 / 2, 0, 0, 0]
    ext j
    fin_cases j <;> dsimp [axisSwap]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_taubPoint_preimage (i : Fin 6) (j : Fin 3) :
    ∃ k : Fin 3, (axisFrame i).map (taubPoint k) = taubPoint j := by
  fin_cases i
  · exact ⟨j, by simp [axisFrame_apply]⟩
  · refine ⟨j + 1, ?_⟩
    simp only [axisFrame_apply, axisCycle_taubPoint]
    fin_cases j <;> rfl
  · refine ⟨j + 2, ?_⟩
    simp only [axisFrame_apply, axisCycle_taubPoint]
    fin_cases j <;> rfl
  · refine ⟨-j, ?_⟩
    simp [axisFrame_apply, axisSwap_taubPoint]
  · refine ⟨-j + 1, ?_⟩
    simp only [axisFrame_apply, axisSwap_taubPoint, axisCycle_taubPoint]
    fin_cases j <;> rfl
  · refine ⟨-j + 2, ?_⟩
    simp only [axisFrame_apply, axisSwap_taubPoint, axisCycle_taubPoint]
    fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisFrame_away_taub {x : NormalizedState} {ε : ℝ}
    (haway : ∀ j, ε ≤ normalizedEuclideanDistance x (taubPoint j)) (i : Fin 6) :
    ∀ j, ε ≤ normalizedEuclideanDistance ((axisFrame i).map x) (taubPoint j) := by
  intro j
  obtain ⟨k, hk⟩ := axisFrame_taubPoint_preimage i j
  rw [← hk, axisFrame_euclideanDistance]
  exact haway k

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubAvoidance.initial {ε : ℝ} {x : NormalizedState}
    (H : normalizedTaubAvoidance ε x) : ∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i) := by
  simpa only [normalizedMaxCurve_initial] using H 0 le_rfl (initial_mem_normalizedMaxDomain x 0)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubAvoidance.forward {ε s : ℝ} {x : NormalizedState}
    (H : normalizedTaubAvoidance ε x) (hs : 0 ≤ s) (hdom : s ∈ normalizedMaxDomain x 0) :
    normalizedTaubAvoidance ε (normalizedMaxCurve x 0 s) := by
  intro t ht htime i
  obtain ⟨hfull, heq⟩ := normalizedMaxCurve_restart (t := t + s) hdom (by simpa only [add_sub_cancel_right] using htime)
  simp only [add_sub_cancel_right] at heq
  rw [← heq]
  exact H _ (add_nonneg ht hs) hfull i

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubAvoidance.frame {ε : ℝ} {x : NormalizedState}
    (H : normalizedTaubAvoidance ε x) (i : Fin 6) :
    normalizedTaubAvoidance ε ((axisFrame i).map x) := by
  intro t ht hdom j
  rw [(axisFrame i).maxDomain] at hdom
  rw [(axisFrame i).maxCurve hdom]
  exact axisFrame_away_taub (H t ht hdom) i j

end
end


/-- Uniformly small future wall products and Taub avoidance force a core on the original orbit. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ Δ₀ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ Δ ∈ Icc 0 Δ₀,
      ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
        normalizedTaubAvoidance ε x →
        (∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
        ∃ s > (0 : ℝ), ∃ T > s, ∃ a : Fin 6, ∃ k : ℝ,
          2 ≤ k ∧ k < 8 / ε ∧ T - s ≤ C ∧ T ∈ normalizedMaxDomain x 0 ∧
          let X := (axisFrame a).map (normalizedMaxCurve x 0 T)
          let Y := toProjectiveState X
          IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧
            projectiveActiveWall ((axisFrame a).map (normalizedMaxCurve x 0 t)) = 1} T ∧
          Y 2 = 1 ∧ 1 < Y 0 ∧ 0 < 1 + X 0 ∧
          |coreRadius (Y 0) (Y 2) - k| ≤ C * Δ ^ 2 ∧
          referenceCoreWallFloor (8 / ε) ≤ X 3 ∧
          0 < Y 1 ∧ 0 < Y 3 ∧
          Y 1 + Y 3 ≤ Δ ^ 2 / (2 * referenceCoreWallFloor (8 / ε) ^ 2) ∧
          0 < fderiv ℝ projectiveActiveWall X (normalizedField X) ∧
          normalizedTaubAvoidance ε X := by
  obtain ⟨ν₀, hν₀, hν₀max, c, hcpos, _, Hentry⟩ := exists_late_fixedWall_entrance hε
  let ν := min ν₀ (min (c / 4) (ε ^ 2 / 32))
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνcap : ν ≤ ν₀ := min_le_left _ _
  have hνmax : ν ≤ 1 / 4 := hνcap.trans hν₀max
  have hνc : ν ^ 2 ≤ c / 4 := by
    have H : ν ≤ c / 4 := (min_le_right _ _).trans (min_le_left _ _)
    nlinarith only [hν, hνmax, H]
  have hνε : ν ≤ ε ^ 2 / 32 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Δ₁, hΔ₁, C, hC, Hcore⟩ := exists_fixedWall_physical_core hcpos hε hν hνmax hνc hνε
  refine ⟨min Δ₁ (ν / 8), lt_min hΔ₁ (by positivity), C, hC, ?_⟩
  intro Δ hΔ x hc hp ha hprod
  obtain ⟨r, hr, s, hrs, i, _, _, _, hhit, _, hrate, _⟩ :=
    Hentry ν hν hνcap Δ hΔ.1 (hΔ.2.trans (min_le_right _ _)) x hc hp ha hprod
  have hs : 0 < s := hr.1.trans_lt hrs
  have hdoms := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hs.le
  let x₀ := normalizedMaxCurve x 0 s
  have hc₀ : stateConstraint x₀ = 1 := (normalizedMaxCurve_constraint hdoms).trans hc
  have hp₀ : positiveWalls x₀ := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain x 0)
    hdoms (by simpa only [normalizedMaxCurve_initial] using hp)
  obtain ⟨j, hj⟩ := exists_axisFrame_first_wall i
  let y := (axisFrame j).map x₀
  have hcy : stateConstraint y = 1 := ((axisFrame j).constraint x₀).trans hc₀
  have hpy : positiveWalls y := ((axisFrame j).positive x₀).mpr hp₀
  have hay : normalizedTaubAvoidance ε y := (ha.forward hs.le hdoms).frame j
  have hny : y 2 = ν := by
    change wallValue 0 ((axisFrame j).map x₀) = ν
    rw [axisFrame_wallValue, hj]
    exact hhit
  have hry : c ≤ rateOne (y 0) (y 1) := by
    change c ≤ wallRate 0 ((axisFrame j).map x₀)
    rw [axisFrame_wallRate hp₀, hj]
    exact hrate
  have hprody (u : ℝ) (hu : 0 ≤ u) : normalizedWallProductsBound Δ (normalizedMaxCurve y 0 u) := by
    rw [(axisFrame j).maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc₀ 0 hu)]
    exact (normalizedWallProductsBound.forward hc hprod hs.le u hu).axisFrame j
  obtain ⟨b, k, τ, hk, hkε, _, hfirst, hτC, horbit, hV, hM, hA, hphase, hwall,
    hU, hW, hweak, _, htrans, _⟩ := Hcore Δ ⟨hΔ.1, hΔ.2.trans (min_le_left _ _)⟩
      y hcy hpy hny hry hay.initial hprody
  obtain ⟨a, hcomp⟩ := axisFrame_comp b j
  let z := (axisFrame b).map y
  have hez : z = (axisFrame a).map x₀ := hcomp x₀
  have hcz : stateConstraint z = 1 := ((axisFrame b).constraint y).trans hcy
  have hrestart (u : ℝ) (hu : s ≤ u) :
      normalizedMaxCurve z 0 (u - s) = (axisFrame a).map (normalizedMaxCurve x 0 u) := by
    rw [hez, (axisFrame a).maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc₀ 0 (sub_nonneg.mpr hu))]
    rw [(normalizedMaxCurve_restart hdoms
      (normalizedMaxDomain_contains_Ici_of_constraint hc₀ 0 (sub_nonneg.mpr hu))).2]
  have hτ : 0 < τ := hfirst.1.1
  let T := s + τ
  have hTs : s < T := by dsimp [T]; linarith only [hτ]
  have hdomT := normalizedMaxDomain_contains_Ici_of_constraint hc 0 (hs.le.trans hTs.le)
  have hend : normalizedMaxCurve z 0 τ = (axisFrame a).map (normalizedMaxCurve x 0 T) := by
    simpa only [T, add_sub_cancel_left] using hrestart T hTs.le
  let X := (axisFrame a).map (normalizedMaxCurve x 0 T)
  let Y := toProjectiveState X
  have hleast : IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧
      projectiveActiveWall ((axisFrame a).map (normalizedMaxCurve x 0 t)) = 1} T := by
    refine ⟨⟨hTs, hdomT, ?_⟩, ?_⟩
    · rw [← hend]
      exact hfirst.1.2.2
    · intro u hu
      have hh : projectiveActiveWall (normalizedMaxCurve z 0 (u - s)) = 1 := by
        rw [hrestart u hu.1.le]
        exact hu.2.2
      have H := hfirst.2 ⟨sub_pos.mpr hu.1,
        normalizedMaxDomain_contains_Ici_of_constraint hcz 0 (sub_pos.mpr hu.1).le, hh⟩
      dsimp [T]
      linarith only [H]
  have htrans' : 0 < fderiv ℝ projectiveActiveWall X (normalizedField X) := by
    change 0 < fderiv ℝ projectiveActiveWall (normalizedMaxCurve z 0 τ)
      (normalizedField (normalizedMaxCurve z 0 τ)) at htrans
    simpa only [hend] using htrans
  refine ⟨s, hs, T, hTs, a, k, hk, hkε, ?_, hdomT, hleast, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htrans',
    (ha.forward (hs.le.trans hTs.le) hdomT).frame a⟩
  · simpa only [T, add_sub_cancel_left] using hτC
  all_goals rw [← hend]; assumption
