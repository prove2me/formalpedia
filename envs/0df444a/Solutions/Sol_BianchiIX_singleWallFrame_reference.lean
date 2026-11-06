-- Prove2me | solution 1 for BianchiIX.singleWallFrame_reference
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:06:57.148665+00:00
-- url     : https://prove2.me/submissions/0517677e-8688-47a9-b14d-084a5e374b3d

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_projectiveDenom_of_constraint
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact

noncomputable section
open BianchiIX

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

private theorem BianchiIX.singleWallFrame_coordinates {x : NormalizedState} (h3 : x 3 = 0) (h4 : x 4 = 0) :
    (axisFrame (singleWallFrame x)).map x =
      ![-(x 0 + Real.sqrt 3 * |x 1|) / 2, (Real.sqrt 3 * x 0 - |x 1|) / 2, 0, x 2, 0] := by
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  by_cases hs : 0 ≤ x 1
  · rw [singleWallFrame, if_pos hs, axisFrame_apply, abs_of_nonneg hs]
    change axisCycle (axisCycle x) = _
    ext i
    fin_cases i <;> simp [axisCycle, h3, h4] <;> ring_nf <;> norm_num [hr] <;> ring
  · rw [singleWallFrame, if_neg hs, axisFrame_apply, abs_of_neg (lt_of_not_ge hs)]
    change axisSwap (axisCycle x) = _
    ext i
    fin_cases i <;> simp [axisCycle, axisSwap, h3, h4] <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleWallFrame_chart {x : NormalizedState}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0) (hn : 0 < x 2) :
    0 < 1 + (axisFrame (singleWallFrame x)).map x 0 := by
  let z := (axisFrame (singleWallFrame x)).map x
  have hz := ((axisFrame (singleWallFrame x)).constraint x).trans hc
  have he := singleWallFrame_coordinates h3 h4
  have hsq : z 0 ^ 2 + z 1 ^ 2 + x 2 ^ 2 = 1 := by
    change stateConstraint z = 1 at hz
    have h2 : z 2 = 0 := by rw [show z = _ from he]; rfl
    have h3' : z 3 = x 2 := by rw [show z = _ from he]; rfl
    have h4' : z 4 = 0 := by rw [show z = _ from he]; rfl
    simpa [stateConstraint, constraint, shearSq, curvature, h2, h3', h4'] using hz
  change 0 < 1 + z 0
  nlinarith only [hsq, sq_pos_of_pos hn, sq_nonneg (z 1), sq_nonneg (z 0 + 1)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleWallFrame_taubDistance {x : NormalizedState}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0) :
    normalizedEuclideanDistance ((axisFrame (singleWallFrame x)).map x) (taubPoint 0) ^ 2 =
      2 * (1 + (axisFrame (singleWallFrame x)).map x 0) := by
  let z := (axisFrame (singleWallFrame x)).map x
  have hz := ((axisFrame (singleWallFrame x)).constraint x).trans hc
  rw [singleWallFrame_coordinates h3 h4] at hz
  simp [stateConstraint, constraint, shearSq, curvature] at hz
  rw [normalizedEuclideanDistance_sq, singleWallFrame_coordinates h3 h4]
  simp [Fin.sum_univ_succ, taubPoint]
  nlinarith only [hz]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleWallFrame_projective_identities {x : NormalizedState}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0) (hn : 0 < x 2) :
    let z := (axisFrame (singleWallFrame x)).map x
    let y := toProjectiveState z
    y 1 = 0 ∧ y 3 = 0 ∧ y 2 = Real.sqrt 3 * x 2 / (1 + z 0) ∧
      (y 0 - 1) * (1 + z 0) = 2 * x 0 - 1 ∧
      ((y 0 - 1) ^ 2 + y 2 ^ 2) * (1 + z 0) = 4 * (1 + z 0) + 4 * Real.sqrt 3 * |x 1| := by
  dsimp only
  let z := (axisFrame (singleWallFrame x)).map x
  let y := toProjectiveState z
  have hA := singleWallFrame_chart hc h3 h4 hn
  change 0 < 1 + z 0 at hA
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : x 0 ^ 2 + |x 1| ^ 2 + x 2 ^ 2 = 1 := by
    simpa [stateConstraint, constraint, shearSq, curvature, h3, h4] using hc
  have he := singleWallFrame_coordinates h3 h4
  have hz0 : z 0 = -(x 0 + Real.sqrt 3 * |x 1|) / 2 := congrFun he 0
  have hz1 : z 1 = (Real.sqrt 3 * x 0 - |x 1|) / 2 := congrFun he 1
  have hz3 : z 3 = x 2 := congrFun he 3
  have hM : y 0 * (1 + z 0) = Real.sqrt 3 * z 1 := div_mul_cancel₀ _ hA.ne'
  have hV : y 2 * (1 + z 0) = Real.sqrt 3 * x 2 := by
    change (Real.sqrt 3 * z 3 / (1 + z 0)) * (1 + z 0) = _
    rw [div_mul_cancel₀ _ hA.ne', hz3]
  have hm : (y 0 - 1) * (1 + z 0) = 2 * x 0 - 1 := by
    calc
      _ = Real.sqrt 3 * z 1 - (1 + z 0) := by nlinarith only [hM]
      _ = _ := by rw [hz0, hz1]; ring_nf; rw [hr]; ring
  refine ⟨?_, ?_, ?_, hm, ?_⟩
  · simp [singleWallFrame_coordinates h3 h4, toProjectiveState, projectiveCoord]
  · simp [singleWallFrame_coordinates h3 h4, toProjectiveState, projectiveCoord]
  · simp [singleWallFrame_coordinates h3 h4, toProjectiveState, projectiveCoord]
  · change ((y 0 - 1) ^ 2 + y 2 ^ 2) * (1 + z 0) = 4 * (1 + z 0) + 4 * Real.sqrt 3 * |x 1|
    apply mul_left_injective₀ hA.ne'
    dsimp only
    calc
      _ = ((y 0 - 1) * (1 + z 0)) ^ 2 + (y 2 * (1 + z 0)) ^ 2 := by ring
      _ = (2 * x 0 - 1) ^ 2 + 3 * x 2 ^ 2 := by rw [hm, hV, mul_pow, hr]
      _ = _ := by
        rw [hz0]
        ring_nf
        rw [hr]
        nlinarith only [hsq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.singleWallFrame_projective_bounds {x : NormalizedState}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hn : 0 < x 2) (hp : 1 / 2 < x 0) :
    let z := (axisFrame (singleWallFrame x)).map x
    let y := toProjectiveState z
    1 < y 0 ∧ 0 < y 2 ∧ 2 ≤ coreRadius (y 0) (y 2) := by
  dsimp only
  let z := (axisFrame (singleWallFrame x)).map x
  let y := toProjectiveState z
  obtain ⟨_, _, hv, hm, hk⟩ := singleWallFrame_projective_identities hc h3 h4 hn
  have hA := singleWallFrame_chart hc h3 h4 hn
  have hm' : 1 < y 0 := by change (y 0 - 1) * (1 + z 0) = _ at hm; nlinarith only [hm, hA, hp]
  have hv' : 0 < y 2 := by change y 2 = _ at hv; rw [hv]; positivity
  have hksq : 4 ≤ (y 0 - 1) ^ 2 + y 2 ^ 2 := by
    change ((y 0 - 1) ^ 2 + y 2 ^ 2) * (1 + z 0) = _ at hk
    have H : 0 ≤ 4 * Real.sqrt 3 * |x 1| := by positivity
    nlinarith only [hk, H, hA]
  refine ⟨hm', hv', ?_⟩
  exact Real.le_sqrt_of_sq_le (by norm_num at hksq ⊢; exact hksq)

end
end


/-- A small physical wall away from Taub gives a compact reference entrance directly. -/
theorem solution {x : NormalizedState} {ε : ℝ}
    (hc : stateConstraint x = 1) (h3 : x 3 = 0) (h4 : x 4 = 0)
    (hn : 0 < x 2) (hp : 1 / 2 < x 0) (hε : 0 < ε)
    (hsmall : x 2 ≤ ε ^ 2 / 8)
    (haway : ∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i)) :
    let z := (axisFrame (singleWallFrame x)).map x
    let y := toProjectiveState z
    let k := coreRadius (y 0) (y 2)
    2 ≤ k ∧ k < 4 / ε ∧ x 2 / 2 ≤ y 2 ∧ y 2 ≤ 1 / 2 ∧
      z = fromProjectiveState (referenceEntranceState k (y 2)) := by
  intro z y k
  have hA : 0 < 1 + z 0 := singleWallFrame_chart hc h3 h4 hn
  have hcon : stateConstraint z = 1 := ((axisFrame (singleWallFrame x)).constraint x).trans hc
  obtain ⟨hu, hw, hv, _, _⟩ := singleWallFrame_projective_identities hc h3 h4 hn
  change y 1 = 0 at hu
  change y 3 = 0 at hw
  change y 2 = Real.sqrt 3 * x 2 / (1 + z 0) at hv
  obtain ⟨hm, hv0, hk⟩ := singleWallFrame_projective_bounds hc h3 h4 hn hp
  change 1 < y 0 at hm
  change 0 < y 2 at hv0
  change 2 ≤ k at hk
  have hd := (axisFrame_away_taub haway (singleWallFrame x)) 0
  change ε ≤ normalizedEuclideanDistance z (taubPoint 0) at hd
  have hd2 : ε ^ 2 ≤ normalizedEuclideanDistance z (taubPoint 0) ^ 2 :=
    (sq_le_sq₀ hε.le (normalizedEuclideanDistance_nonneg _ _)).mpr hd
  have hdist : normalizedEuclideanDistance z (taubPoint 0) ^ 2 = 2 * (1 + z 0) :=
    singleWallFrame_taubDistance hc h3 h4
  have hAlo : ε ^ 2 / 2 ≤ 1 + z 0 := by linarith only [hd2, hdist]
  have hD : 3 + y 0 ^ 2 + y 2 ^ 2 = 6 / (1 + z 0) := by
    have H : projectiveStateDenom y = 6 / (1 + z 0) := projectiveDenom_of_constraint hA.ne' hcon
    simpa [projectiveStateDenom, projectiveDenom, curvature, hu, hw] using H
  have hDA := (eq_div_iff hA.ne').mp hD
  have hAhi : 1 + z 0 ≤ 2 := by
    have H : 3 ≤ 3 + y 0 ^ 2 + y 2 ^ 2 := by nlinarith only [sq_nonneg (y 0), sq_nonneg (y 2)]
    nlinarith only [mul_le_mul_of_nonneg_right H hA.le, hDA]
  have hksq : k ^ 2 = (y 0 - 1) ^ 2 + y 2 ^ 2 := Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hkD : k ^ 2 < 3 + y 0 ^ 2 + y 2 ^ 2 := by nlinarith only [hksq, hm]
  have hkA : k ^ 2 * (1 + z 0) < 6 := by
    nlinarith only [mul_lt_mul_of_pos_right hkD hA, hDA]
  have hkε : k < 4 / ε := by
    apply (lt_div_iff₀ hε).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hAlo (sq_nonneg k), hkA, hk, hε]
  have hr : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hrlo : 1 ≤ Real.sqrt 3 := by nlinarith only [hr, hr0]
  have hrhi : Real.sqrt 3 ≤ 2 := by nlinarith only [hr, hr0]
  have hvlo : x 2 / 2 ≤ y 2 := by
    rw [hv]
    apply (le_div_iff₀ hA).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hAhi hn.le,
      mul_le_mul_of_nonneg_right hrlo hn.le]
  have hvhi : y 2 ≤ 1 / 2 := by
    rw [hv]
    apply (div_le_iff₀ hA).mpr
    nlinarith only [hsmall, hAlo, mul_le_mul_of_nonneg_right hrhi hn.le]
  refine ⟨hk, hkε, hvlo, hvhi, ?_⟩
  have hroot : Real.sqrt (k ^ 2 - y 2 ^ 2) = y 0 - 1 := by
    rw [hksq, add_sub_cancel_right, Real.sqrt_sq (by linarith only [hm])]
  have he : referenceEntranceState k (y 2) = y := by
    ext i
    fin_cases i
    · change 1 + Real.sqrt (k ^ 2 - y 2 ^ 2) = y 0
      linarith only [hroot]
    · exact hu.symm
    · rfl
    · exact hw.symm
  rw [he]
  exact (fromProjectiveState_toProjectiveState hA.ne' hcon).symm
