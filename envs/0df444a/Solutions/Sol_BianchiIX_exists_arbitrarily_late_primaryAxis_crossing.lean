-- Prove2me | solution 1 for BianchiIX.exists_arbitrarily_late_primaryAxis_crossing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:09:26.885199+00:00
-- url     : https://prove2.me/submissions/2f4e2daa-d37c-4844-ab22-ed68529baf94

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_exists_arbitrarily_late_taub_section_crossing
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.ByContra
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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

private theorem BianchiIX.axisPermutation_walls (σ : Equiv.Perm (Fin 3)) (x : NormalizedState) :
    normalizedWalls ((axisPermutation σ).map x) = fun j => normalizedWalls x (σ j) := by
  rw [axisPermutation, axisFrame_walls]
  funext j
  rw [(axisOrder_covers σ).choose_spec j]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisPermutation_shears (σ : Equiv.Perm (Fin 3)) (x : NormalizedState) :
    normalizedShears ((axisPermutation σ).map x) = fun j => normalizedShears x (σ j) := by
  rw [axisPermutation, axisFrame_shears]
  funext j
  rw [(axisOrder_covers σ).choose_spec j]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisPermutation_maxCurve (σ : Equiv.Perm (Fin 3)) {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve ((axisPermutation σ).map x) t₀ t =
      (axisPermutation σ).map (normalizedMaxCurve x t₀ t) :=
  (axisPermutation σ).maxCurve ht

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

private theorem BianchiIX.normalizedState_eq_of_shears_walls {x y : NormalizedState}
    (hs : normalizedShears x = normalizedShears y) (hw : normalizedWalls x = normalizedWalls y) :
    x = y := by
  have hp := congrFun hs 0
  have hq := congrFun hs 1
  simp [normalizedShears] at hp hq
  have hp' : x 0 = y 0 := by linarith only [hp]
  have hq' : x 1 = y 1 := by
    have hn : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
    apply mul_left_cancel₀ hn
    linarith only [hp', hq]
  ext j
  fin_cases j
  · exact hp'
  · exact hq'
  · exact congrFun hw 0
  · exact congrFun hw 1
  · exact congrFun hw 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedShears_taubPoint (i j : Fin 3) :
    normalizedShears (taubPoint i) j = if j = i then 2 else -1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;> simp [taubPoint, normalizedShears] <;>
    nlinarith only [hs]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedWalls_taubPoint (i : Fin 3) : normalizedWalls (taubPoint i) = 0 := by
  fin_cases i <;> ext j <;> fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisPermutation_taubPoint (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    (axisPermutation σ).map (taubPoint i) = taubPoint (σ.symm i) := by
  apply normalizedState_eq_of_shears_walls
  · rw [axisPermutation_shears]
    ext j
    simp only [normalizedShears_taubPoint, Equiv.eq_symm_apply]
  · rw [axisPermutation_walls, normalizedWalls_taubPoint, normalizedWalls_taubPoint]
    rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.primaryAxisFrame_taubPoint (i : Fin 3) :
    (primaryAxisFrame i).map (taubPoint i) = taubPoint 0 := by
  simp [primaryAxisFrame, axisPermutation_taubPoint]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisPermutation_euclideanDistance (σ : Equiv.Perm (Fin 3)) (x y : NormalizedState) :
    normalizedEuclideanDistance ((axisPermutation σ).map x) ((axisPermutation σ).map y) =
      normalizedEuclideanDistance x y :=
  axisFrame_euclideanDistance _ x y

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisPermutation_wallValue (σ : Equiv.Perm (Fin 3)) (x : NormalizedState) (i : Fin 3) :
    wallValue i ((axisPermutation σ).map x) = wallValue (σ i) x := by
  have heq (y : NormalizedState) (j : Fin 3) : normalizedWalls y j = wallValue j y := by
    fin_cases j <;> rfl
  simpa only [heq] using congrFun (axisPermutation_walls σ x) i

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_fixed_late_taub_target {α : ℝ → NormalizedState}
    (H : ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R, ∃ i : Fin 3,
      normalizedEuclideanDistance (α t) (taubPoint i) < ε) :
    ∃ i : Fin 3, ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R,
      normalizedEuclideanDistance (α t) (taubPoint i) < ε := by
  classical
  by_contra! hn
  choose ε hε R hR using hn
  obtain ⟨t, ht, i, hi⟩ := H (min (ε 0) (min (ε 1) (ε 2)))
    (lt_min (hε 0) (lt_min (hε 1) (hε 2))) (max (R 0) (max (R 1) (R 2)))
  have hti : R i ≤ t := by
    apply le_trans _ ht
    fin_cases i
    · exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  have hei : min (ε 0) (min (ε 1) (ε 2)) ≤ ε i := by
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  exact (not_lt_of_ge (hR i t hti)) (hi.trans_le hei)

end
end

private theorem BianchiIX.wallProductDecay_axisPermutation {x : NormalizedState}
    (hp : positiveWalls x) (hc : stateConstraint x = 1)
    (hprod : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t))
        atTop (𝓝 0)) (σ : Equiv.Perm (Fin 3)) :
    ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve ((axisPermutation σ).map x) 0 t) *
        wallValue j (normalizedMaxCurve ((axisPermutation σ).map x) 0 t)) atTop (𝓝 0) := by
  intro i j hij
  apply (hprod (σ i) (σ j) (σ.injective.ne hij)).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [axisPermutation_maxCurve σ (normalizedMaxDomain_contains_Ici hp hc 0 ht),
    axisPermutation_wallValue, axisPermutation_wallValue]


/-- Late Taub approaches give late physical crossings of one fixed member of the three-axis family. -/
theorem solution {x : NormalizedState} {h d : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hr : ∀ i, 0 < normalizedTaubRadiusSq ((primaryAxisFrame i).map x))
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hprod : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t))
        atTop (𝓝 0))
    (hvisit : ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R, ∃ i : Fin 3,
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint i) < ε) :
    ∃ i : Fin 3, ∀ R : ℝ, ∀ η > (0 : ℝ), ∃ c > max R 0,
      c ∈ normalizedMaxDomain x 0 ∧ ∃ y ∈ mainWallChartDomain h,
        axisWallChart (primaryAxisFrame i) h y = normalizedMaxCurve x 0 c ∧
        |y 0| < d ∧ Real.exp (-y 1) < d ∧ Real.exp (-y 2) < d ∧
        normalizedTaubRadiusSq ((primaryAxisFrame i).map (normalizedMaxCurve x 0 c)) < η := by
  obtain ⟨i, hi⟩ := exists_fixed_late_taub_target hvisit
  have hvisit' : ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R,
      normalizedEuclideanDistance (normalizedMaxCurve ((primaryAxisFrame i).map x) 0 t)
        (taubPoint 0) < ε := by
    intro ε hε R
    obtain ⟨t, ht, hti⟩ := hi ε hε (max R 0)
    refine ⟨t, (le_max_left R 0).trans ht, ?_⟩
    rw [(primaryAxisFrame i).maxCurve
      (normalizedMaxDomain_contains_Ici hp hc 0 ((le_max_right R 0).trans ht)),
      ← primaryAxisFrame_taubPoint i]
    exact (axisPermutation_euclideanDistance _ _ _).trans_lt hti
  have hcross := exists_arbitrarily_late_taub_section_crossing
    ((primaryAxisFrame i).constraint x |>.trans hc) ((primaryAxisFrame i).positive x |>.mpr hp)
    (hr i) hh hhmax hd hdh (wallProductDecay_axisPermutation hp hc hprod _) hvisit'
  refine ⟨i, fun R η hη => ?_⟩
  obtain ⟨c, hcR, hdom, y, hy, hchart, hs, hb, hw, hrad, _⟩ := hcross R η hη
  rw [(primaryAxisFrame i).maxDomain] at hdom
  rw [(primaryAxisFrame i).maxCurve hdom] at hchart hrad
  refine ⟨c, hcR, hdom, y, hy, ?_, hs, hb, hw, hrad⟩
  exact (primaryAxisFrame i).map.injective (by simpa [axisWallChart] using hchart)
