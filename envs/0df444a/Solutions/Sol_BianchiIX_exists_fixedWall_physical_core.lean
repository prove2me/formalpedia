-- Prove2me | solution 1 for BianchiIX.exists_fixedWall_physical_core
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:10:57.332328+00:00
-- url     : https://prove2.me/submissions/dee97a3a-6372-44a3-a0c9-8ed4100041cd

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_exists_compact_physicalEntrance_core
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_positive_walls_invariant
import Theorems.Thm_BianchiIX_normalized_singleWall_projection
import Theorems.Thm_BianchiIX_singleWallFrame_reference
import Theorems.Thm_BianchiIX_toProjectiveState_positive
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
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set

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

private theorem BianchiIX.singleWall_projection_growth {x : NormalizedState} {Δ c : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hnmax : x 2 ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ x 2 / 8)
    (hprod : normalizedWallProductsBound Δ x)
    (hgrowth : c ≤ rateOne (x 0) (x 1)) (hsmall : Δ ^ 2 ≤ c / 18) :
    c / 2 ≤ rateOne (singleWallProjection x 0) (singleWallProjection x 1) := by
  have H := (normalized_singleWall_projection hc hp hnmax hΔ hprod).2.2.2.2.2.2
  have Hlo := (abs_le.mp H).1
  linarith only [Hlo, hgrowth, hsmall]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.projected_singleWall_reference {x : NormalizedState} {Δ c ε : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hnmax : x 2 ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ x 2 / 8)
    (hprod : normalizedWallProductsBound Δ x) (hcpos : 0 < c) (hε : 0 < ε)
    (hr : c ≤ rateOne (x 0) (x 1)) (hΔc : Δ ^ 2 ≤ c / 18)
    (hnc : x 2 ^ 2 ≤ c / 4) (hnε : x 2 ≤ ε ^ 2 / 32)
    (hclose : 2 * Δ ^ 2 / x 2 ≤ ε / 2)
    (haway : ∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i)) :
    ∃ a : Fin 6, ∃ k v : ℝ, 2 ≤ k ∧ k < 8 / ε ∧ x 2 / 2 ≤ v ∧ v ≤ 1 / 2 ∧
      (axisFrame a).map (singleWallProjection x) = fromProjectiveState (referenceEntranceState k v) ∧
      normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) ((axisFrame a).map x) ≤
        2 * Δ ^ 2 / x 2 := by
  let y := singleWallProjection x
  have H := normalized_singleWall_projection hc hp hnmax hΔ hprod
  have hrate : c / 2 ≤ rateOne (y 0) (y 1) := singleWall_projection_growth hc hp hnmax hΔ hprod hr hΔc
  have hycon : constraint (y 0) (y 1) (x 2) 0 0 = 1 := H.1
  have hyp : 1 / 2 < y 0 := by
    dsimp [constraint, shearSq, curvature] at hycon
    dsimp [rateOne, shearSq] at hrate
    nlinarith only [hycon, hrate, hnc, hcpos]
  have hyd : normalizedEuclideanDistance y x ≤ 2 * Δ ^ 2 / x 2 := H.2.2.2.2.2.1
  have hyaway (i : Fin 3) : ε / 2 ≤ normalizedEuclideanDistance y (taubPoint i) := by
    have Htri : normalizedEuclideanDistance x (taubPoint i) ≤
        normalizedEuclideanDistance y x + normalizedEuclideanDistance y (taubPoint i) := by
      have H' : normalizedEuclideanDistance x (taubPoint i) ≤
          normalizedEuclideanDistance x y + normalizedEuclideanDistance y (taubPoint i) := dist_triangle _ _ _
      have Hsym : normalizedEuclideanDistance x y = normalizedEuclideanDistance y x := dist_comm _ _
      rwa [Hsym] at H'
    linarith only [Htri, haway i, hyd, hclose]
  have hnε' : y 2 ≤ (ε / 2) ^ 2 / 8 := by change x 2 ≤ _; nlinarith only [hnε]
  have HR := singleWallFrame_reference H.1 H.2.2.1 H.2.2.2.1 hp.1 hyp (half_pos hε) hnε' hyaway
  let a := singleWallFrame y
  let z := (axisFrame a).map y
  let q := toProjectiveState z
  let k := coreRadius (q 0) (q 2)
  change 2 ≤ k ∧ k < 4 / (ε / 2) ∧ y 2 / 2 ≤ q 2 ∧ q 2 ≤ 1 / 2 ∧
    z = fromProjectiveState (referenceEntranceState k (q 2)) at HR
  refine ⟨a, k, q 2, HR.1, ?_, HR.2.2.1, HR.2.2.2.1, HR.2.2.2.2, ?_⟩
  · convert HR.2.1 using 1
    ring
  · rw [← HR.2.2.2.2]
    change normalizedEuclideanDistance ((axisFrame a).map y) ((axisFrame a).map x) ≤ _
    rw [axisFrame_euclideanDistance]
    exact hyd

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceCoreWallFloor_pos (K : ℝ) : 0 < referenceCoreWallFloor K := by
  unfold referenceCoreWallFloor
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.physical_core_weak_sum {x : NormalizedState} {Δ n : ℝ}
    (hp : positiveWalls x) (hA : 0 < 1 + x 0) (hv : toProjectiveState x 2 = 1)
    (hprod : normalizedWallProductsBound Δ x) (hn : 0 < n) (hwall : n ≤ x 3) :
    0 < toProjectiveState x 1 ∧ 0 < toProjectiveState x 3 ∧
      toProjectiveState x 1 + toProjectiveState x 3 ≤ Δ ^ 2 / (2 * n ^ 2) := by
  have hrt : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hscale : 1 + x 0 = Real.sqrt 3 * x 3 := by
    change Real.sqrt 3 * x 3 / (1 + x 0) = 1 at hv
    have H := (div_eq_iff hA.ne').mp hv
    linarith only [H]
  have hU : toProjectiveState x 1 = x 2 / x 3 := by
    change Real.sqrt 3 * x 2 / (1 + x 0) = _
    rw [hscale]
    field_simp
  have hW : toProjectiveState x 3 = x 4 / x 3 := by
    change Real.sqrt 3 * x 4 / (1 + x 0) = _
    rw [hscale]
    field_simp
  obtain ⟨hup, _, hwp⟩ := toProjectiveState_positive hA hp
  refine ⟨hup, hwp, ?_⟩
  have hsum : (toProjectiveState x 1 + toProjectiveState x 3) * x 3 = x 2 + x 4 := by
    rw [hU, hW]
    field_simp [hp.2.1.ne']
  have hprod' : 2 * x 3 * (x 2 + x 4) ≤ Δ ^ 2 := by nlinarith only [hprod.1, hprod.2.1]
  have hnsq : n ^ 2 ≤ x 3 ^ 2 := (sq_le_sq₀ hn.le hp.2.1.le).mpr hwall
  apply (le_div_iff₀ (by positivity : 0 < 2 * n ^ 2)).mpr
  have H := mul_le_mul_of_nonneg_left hnsq (add_pos hup hwp).le
  have hsum2 := congrArg (fun r : ℝ => r * x 3) hsum
  nlinarith only [H, hsum2, hprod']

end
end


/-- A fixed-height growing wall reaches a genuine core on the same Einstein orbit, with quadratic errors. -/
theorem solution {c ε ν : ℝ}
    (hcpos : 0 < c) (hε : 0 < ε) (hν : 0 < ν) (hνmax : ν ≤ 1 / 4)
    (hνc : ν ^ 2 ≤ c / 4) (hνε : ν ≤ ε ^ 2 / 32) :
    ∃ Δ₀ > (0 : ℝ), ∃ C ≥ (1 : ℝ), ∀ Δ ∈ Icc 0 Δ₀,
      ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x → x 2 = ν →
        c ≤ rateOne (x 0) (x 1) →
        (∀ i, ε ≤ normalizedEuclideanDistance x (taubPoint i)) →
        (∀ u, 0 ≤ u → normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
        ∃ a : Fin 6, ∃ k T : ℝ, 2 ≤ k ∧ k < 8 / ε ∧ T ∈ normalizedMaxDomain x 0 ∧
          let z := (axisFrame a).map x
          let X := normalizedMaxCurve z 0 T
          let Y := toProjectiveState X
          IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain z 0 ∧ projectiveActiveWall (normalizedMaxCurve z 0 t) = 1} T ∧
            T ≤ C ∧ X = (axisFrame a).map (normalizedMaxCurve x 0 T) ∧
            Y 2 = 1 ∧ 1 < Y 0 ∧ 0 < 1 + X 0 ∧
            |coreRadius (Y 0) (Y 2) - k| ≤ C * Δ ^ 2 ∧
            referenceCoreWallFloor (8 / ε) ≤ X 3 ∧
            0 < Y 1 ∧ 0 < Y 3 ∧
            Y 1 + Y 3 ≤ Δ ^ 2 / (2 * referenceCoreWallFloor (8 / ε) ^ 2) ∧
            HasDerivAt (fun t => projectiveActiveWall (normalizedMaxCurve z 0 t))
              (normalizedEventRate projectiveActiveWall z 0 T) T ∧
            0 < normalizedEventRate projectiveActiveWall z 0 T ∧
            ContDiffAt ℝ 2 physicalEntranceData z := by
  obtain ⟨δ, hδ, C, hC, H⟩ := exists_compact_physicalEntrance_core (K := 8 / ε) (half_pos hν)
  let Δ₀ := min 1 (min (ν / 8) (min (c / 18) (min (ε * ν / 4) (δ * ν / 2))))
  have hΔ₀ : 0 < Δ₀ := by
    dsimp [Δ₀]
    positivity
  let C' := max C (2 * C / ν)
  have hCC : C ≤ C' := le_max_left _ _
  have hCnonneg : 0 ≤ C := by linarith only [hC]
  refine ⟨Δ₀, hΔ₀, C', hC.trans hCC, ?_⟩
  intro Δ hΔ x hc hp hn hr haway hprod
  have hΔ1 : Δ ≤ 1 := hΔ.2.trans (min_le_left _ _)
  have hΔν : Δ ≤ ν / 8 := hΔ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hΔc : Δ ≤ c / 18 := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hΔε : Δ ≤ ε * ν / 4 := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hΔδ : Δ ≤ δ * ν / 2 := hΔ.2.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hsq : Δ ^ 2 ≤ Δ := by nlinarith only [hΔ.1, hΔ1]
  have hcloseε : 2 * Δ ^ 2 / ν ≤ ε / 2 := by
    apply (div_le_iff₀ hν).mpr
    nlinarith only [hsq, hΔε]
  have hcloseδ : 2 * Δ ^ 2 / ν ≤ δ := by
    apply (div_le_iff₀ hν).mpr
    nlinarith only [hsq, hΔδ]
  have hprod0 : normalizedWallProductsBound Δ x := by
    simpa only [normalizedMaxCurve_initial] using hprod 0 le_rfl
  obtain ⟨a, k, v, hk, hkε, hvlo, hvhi, _, hdist⟩ := projected_singleWall_reference hc hp
    (hn.symm ▸ hνmax) ⟨hΔ.1, hn.symm ▸ hΔν⟩ hprod0 hcpos hε hr
    (hsq.trans hΔc) (hn.symm ▸ hνc) (hn.symm ▸ hνε) (hn.symm ▸ hcloseε) haway
  rw [hn] at hvlo hdist
  let z := (axisFrame a).map x
  have hcz : stateConstraint z = 1 := ((axisFrame a).constraint x).trans hc
  have hpz : positiveWalls z := ((axisFrame a).positive x).mpr hp
  have HH := H k ⟨hk, hkε.le⟩ v ⟨hvlo, hvhi⟩ z hcz (hdist.trans hcloseδ)
  let T := (physicalEntranceData z).1
  let X := normalizedMaxCurve z 0 T
  let Y := toProjectiveState X
  obtain ⟨hfirst, htime, hV, hM, hA, hphase, hwall, hderiv, hrate, hreg⟩ := HH
  have hdom : T ∈ normalizedMaxDomain x 0 :=
    normalizedMaxDomain_contains_Ici_of_constraint hc 0 hfirst.1.1.le
  have horbit : X = (axisFrame a).map (normalizedMaxCurve x 0 T) := (axisFrame a).maxCurve hdom
  have hprodX : normalizedWallProductsBound Δ X := by
    rw [horbit]
    exact (hprod T hfirst.1.1.le).axisFrame a
  have hpX : positiveWalls X := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain z 0) (isOpen_normalizedMaxDomain z 0)
    (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain z 0)
    hfirst.1.2.1 (by simpa only [normalizedMaxCurve_initial] using hpz)
  obtain ⟨hU, hW, hweak⟩ := physical_core_weak_sum hpX hA hV hprodX
    (referenceCoreWallFloor_pos (8 / ε)) hwall
  have hphase' : |coreRadius (Y 0) (Y 2) - k| ≤ C' * Δ ^ 2 := calc
    _ ≤ C * normalizedEuclideanDistance (fromProjectiveState (referenceEntranceState k v)) z := hphase
    _ ≤ C * (2 * Δ ^ 2 / ν) := mul_le_mul_of_nonneg_left hdist hCnonneg
    _ = (2 * C / ν) * Δ ^ 2 := by ring
    _ ≤ C' * Δ ^ 2 := mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg Δ)
  exact ⟨a, k, T, hk, hkε, hdom, hfirst, htime.trans hCC, horbit, hV, hM, hA,
    hphase', hwall, hU, hW, hweak, hderiv, hrate, hreg⟩
