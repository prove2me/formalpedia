-- Prove2me | solution 1 for BianchiIX.exists_late_fixedWall_entrance
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:09:31.582652+00:00
-- url     : https://prove2.me/submissions/697d81d2-fb05-46a0-b22d-f388b91f60db

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_exists_smallWall_first_upcrossing
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_restart
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_positive_walls_invariant
import Theorems.Thm_BianchiIX_normalized_wall_formula
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

private theorem BianchiIX.constraint_small_wall_products {p s n b c Δ : ℝ}
    (hc : constraint p s n b c = 1)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hbc : 4 * b * c ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2)
    (hΔ : 0 ≤ Δ ∧ Δ ≤ 1 / 4) :
    p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 1 + 3 / 2 * Δ ^ 2 ∧
      p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 35 / 32 ∧ |p| < 17 / 16 := by
  have hsum : p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 1 + 3 / 2 * Δ ^ 2 := by
    dsimp [constraint, shearSq, curvature] at hc
    nlinarith only [hc, hnb, hbc, hcn]
  have hΔsq : Δ ^ 2 ≤ 1 / 16 := by nlinarith only [hΔ.1, hΔ.2]
  have hsum' : p ^ 2 + s ^ 2 + n ^ 2 + b ^ 2 + c ^ 2 ≤ 35 / 32 := by
    linarith only [hsum, hΔsq]
  have hpsq : p ^ 2 < (17 / 16 : ℝ) ^ 2 := by
    nlinarith only [hsum', sq_nonneg s, sq_nonneg n, sq_nonneg b, sq_nonneg c]
  refine ⟨hsum, hsum', abs_lt.mpr ⟨?_, ?_⟩⟩ <;> nlinarith only [hpsq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.weak_wall_sum_of_products {n b c Δ ν : ℝ}
    (hν : 0 < ν) (hn : ν ≤ n) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8)
    (hnb : 4 * n * b ≤ Δ ^ 2) (hcn : 4 * c * n ≤ Δ ^ 2) :
    b + c ≤ Δ ^ 2 / (2 * n) ∧ b + c ≤ ν / 128 := by
  have hnpos : 0 < n := hν.trans_le hn
  have hsum : 2 * n * (b + c) ≤ Δ ^ 2 := by nlinarith only [hnb, hcn]
  have hΔsq : Δ ^ 2 ≤ ν ^ 2 / 64 := by nlinarith only [hΔ.1, hΔ.2, hν]
  have hνsum := mul_le_mul_of_nonneg_right hn (add_nonneg hb hc)
  refine ⟨(le_div_iff₀ (by positivity : 0 < 2 * n)).mpr (by nlinarith only [hsum]), ?_⟩
  nlinarith only [hsum, hΔsq, hνsum, hν]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearPlus_single_wall_descent {p n b c : ℝ}
    (hp : |p| ≤ 17 / 16) (hn : 0 ≤ n) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hweak : b + c ≤ n / 16) : shearPlus p n b c ≤ -(n ^ 2) / 2 := by
  obtain ⟨hplo, hphi⟩ := abs_le.mp hp
  have hmain := mul_le_mul_of_nonneg_right hphi (sq_nonneg n)
  have hcross := mul_le_mul_of_nonneg_right (show 1 - 2 * p ≤ 4 by linarith only [hplo])
    (mul_nonneg hn (add_nonneg hb hc))
  have hdiff : (b - c) ^ 2 ≤ (b + c) ^ 2 := by nlinarith only [mul_nonneg hb hc]
  have hmiddle := (mul_le_mul_of_nonneg_right (show 1 + p ≤ 3 by linarith only [hphi])
    (sq_nonneg (b - c))).trans (mul_le_mul_of_nonneg_left hdiff (by norm_num : (0 : ℝ) ≤ 3))
  have hweakSq : (b + c) ^ 2 ≤ n ^ 2 / 256 := by
    nlinarith only [hweak, hb, hc, hn]
  have hweakProd := mul_le_mul_of_nonneg_left hweak hn
  have heq : shearPlus p n b c =
      (p - 2) * n ^ 2 + (1 + p) * (b - c) ^ 2 + (1 - 2 * p) * n * (b + c) := by
    dsimp [shearPlus, curvature]
    ring
  rw [heq]
  nlinarith only [hmain, hcross, hmiddle, hweakSq, hweakProd, sq_nonneg n]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.hasDerivAt_wallValue {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) (i : Fin 3) :
    HasDerivAt (fun u => wallValue i (α u)) (wallRate i (α t) * wallValue i (α t)) t := by
  have H := hasDerivAt_pi.mp hα (i.addNat 2)
  fin_cases i <;> exact H

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.normalized_wall_pos {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (i : Fin 3) (hpos : 0 < wallValue i (α t₀)) :
    0 < wallValue i (α t) := by
  rw [normalized_wall_formula hI hopen hα ht₀ ht i]
  exact mul_pos hpos (Real.exp_pos _)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_singleWall_estimates {x : NormalizedState} {Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hprod : normalizedWallProductsBound Δ x) (hν : 0 < ν) (hνmax : ν ≤ 1 / 4)
    (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8) (hn : ν ≤ x 2) :
    x 3 + x 4 ≤ Δ ^ 2 / (2 * x 2) ∧ x 3 + x 4 ≤ ν / 128 ∧
      |x 0| < 17 / 16 ∧ normalizedField x 0 ≤ -(x 2 ^ 2) / 2 ∧
      normalizedField x 0 ≤ -(ν ^ 2) / 2 := by
  obtain ⟨hweak, hweak'⟩ := weak_wall_sum_of_products hν hn hp.2.1.le hp.2.2.le hΔ hprod.1 hprod.2.2
  have hΔmax : Δ ≤ 1 / 4 := by linarith only [hΔ.2, hνmax]
  have habs := (constraint_small_wall_products hc hprod.1 hprod.2.1 hprod.2.2 ⟨hΔ.1, hΔmax⟩).2.2
  have hfield : normalizedField x 0 ≤ -(x 2 ^ 2) / 2 :=
    shearPlus_single_wall_descent habs.le hp.1.le hp.2.1.le hp.2.2.le
      (by linarith only [hweak', hn, hν])
  exact ⟨hweak, hweak', habs, hfield, by nlinarith only [hfield, hn, hν]⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_singleWall_residence {x : NormalizedState} {t₀ s t Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hν : 0 < ν) (hνmax : ν ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8)
    (hs : t₀ ≤ s) (hst : s ≤ t)
    (hprod : ∀ u ∈ Icc s t, normalizedWallProductsBound Δ (normalizedMaxCurve x t₀ u))
    (hn : ∀ u ∈ Icc s t, ν ≤ normalizedMaxCurve x t₀ u 2) : t - s < 5 / ν ^ 2 := by
  let p := fun u => normalizedMaxCurve x t₀ u 0
  have H (u : ℝ) (hu : u ∈ Icc s t) :
      |p u| < 17 / 16 ∧ normalizedField (normalizedMaxCurve x t₀ u) 0 ≤ -(ν ^ 2) / 2 := by
    have htime := normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
    have hpos := normalized_positive_walls_invariant
      (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
      (fun u hu => hasDerivAt_normalizedMaxCurve hu)
      (initial_mem_normalizedMaxDomain x t₀) htime
      (by simpa only [normalizedMaxCurve_initial] using hp)
    have he := normalized_singleWall_estimates
      (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).2.1 hpos (hprod u hu) hν hνmax hΔ (hn u hu)
    exact ⟨he.2.2.1, he.2.2.2.2⟩
  have hd (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt p (normalizedField (normalizedMaxCurve x t₀ u) 0) u :=
    hasDerivAt_pi.mp (normalizedMaxCurve_forward_of_constraint hc (hs.trans hu.1)).1 0
  have hdiff := (convex_Icc s t).image_sub_le_mul_sub_of_deriv_le (HasDerivAt.continuousOn hd)
    (fun u hu => (hd u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by rw [(hd u (interior_subset hu)).deriv]; exact (H u (interior_subset hu)).2)
    s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst
  have hps := (abs_lt.mp (H s ⟨le_rfl, hst⟩).1).2
  have hpt := (abs_lt.mp (H t ⟨hst, le_rfl⟩).1).1
  apply (lt_div_iff₀ (sq_pos_of_pos hν)).mpr
  nlinarith only [hdiff, hps, hpt]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_normalized_singleWall_exit {x : NormalizedState} {t₀ s Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hν : 0 < ν) (hνmax : ν ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8) (hs : t₀ ≤ s)
    (hprod : ∀ u ∈ Icc s (s + 5 / ν ^ 2),
      normalizedWallProductsBound Δ (normalizedMaxCurve x t₀ u)) :
    ∃ u ∈ Icc s (s + 5 / ν ^ 2), normalizedMaxCurve x t₀ u 2 < ν := by
  by_contra! H
  have hh := normalized_singleWall_residence hc hp hν hνmax hΔ hs
    (by
      have hlength : 0 < 5 / ν ^ 2 := by positivity
      linarith only [hlength]) hprod H
  linarith only [hh]

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
open Set

private theorem BianchiIX.exists_smallWall_entry_from_first_wall {x : NormalizedState} {Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hν : 0 < ν) (hνmax : ν ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8)
    (hn : ν ≤ x 2)
    (hprod : ∀ u ∈ Icc 0 (5 / ν ^ 2), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) :
    ∃ u ∈ Icc 0 (5 / ν ^ 2), ∀ i : Fin 3, wallValue i (normalizedMaxCurve x 0 u) < ν := by
  obtain ⟨T, hT, hbelow⟩ := exists_normalized_singleWall_exit hc hp hν hνmax hΔ (le_refl 0)
    (by simpa only [zero_add] using hprod)
  simp only [zero_add] at hT
  let n := fun u => normalizedMaxCurve x 0 u 2
  have hpositive : 0 < n T := by
    exact normalized_wall_pos (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
      (fun u hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hT.1) 0
      (by simpa only [normalizedMaxCurve_initial] using! hp.1)
  let r := (ν + n T) / 2
  have hr : ν / 2 ≤ r ∧ r < ν := by dsimp [r, n] at *; constructor <;> linarith only [hpositive, hbelow]
  have hstart : r ≤ n 0 := by simpa only [n, normalizedMaxCurve_initial] using hr.2.le.trans hn
  have hlast : n T ≤ r := by dsimp [r]; linarith only [hbelow]
  have hcont : ContinuousOn n (Icc 0 T) := fun u hu =>
    (hasDerivAt_pi.mp (normalizedMaxCurve_forward_of_constraint hc hu.1).1 2).continuousAt.continuousWithinAt
  obtain ⟨u, hu, heq⟩ := intermediate_value_Icc' hT.1 hcont ⟨hlast, hstart⟩
  have htime := normalizedMaxDomain_contains_Ici_of_constraint hc 0 hu.1
  have hpos := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun v hv => hasDerivAt_normalizedMaxCurve hv) (initial_mem_normalizedMaxDomain x 0) htime
    (by simpa only [normalizedMaxCurve_initial] using hp)
  have hpairs := hprod u ⟨hu.1, hu.2.trans hT.2⟩
  let y := normalizedMaxCurve x 0 u
  have hsum : 2 * y 2 * (y 3 + y 4) ≤ Δ ^ 2 := by
    nlinarith only [hpairs.1, hpairs.2.2]
  have hheight : ν / 2 ≤ y 2 := by change ν / 2 ≤ n u; rw [heq]; exact hr.1
  have hcompare := mul_le_mul_of_nonneg_right hheight (add_nonneg hpos.2.1.le hpos.2.2.le)
  have hΔsq : Δ ^ 2 ≤ ν ^ 2 / 64 := by nlinarith only [hΔ.1, hΔ.2, hν]
  have hweak : y 3 + y 4 < ν := by nlinarith only [hsum, hcompare, hΔsq, hν]
  refine ⟨u, ⟨hu.1, hu.2.trans hT.2⟩, ?_⟩
  intro i
  fin_cases i
  · change n u < ν
    rw [heq]
    exact hr.2
  · change y 3 < ν
    linarith only [hweak, hpos.2.2]
  · change y 4 < ν
    linarith only [hweak, hpos.2.1]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_normalized_smallWall_entry {x : NormalizedState} {Δ ν : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x)
    (hν : 0 < ν) (hνmax : ν ≤ 1 / 4) (hΔ : 0 ≤ Δ ∧ Δ ≤ ν / 8)
    (hprod : ∀ u ∈ Icc 0 (5 / ν ^ 2), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) :
    ∃ u ∈ Icc 0 (5 / ν ^ 2), ∀ i : Fin 3, wallValue i (normalizedMaxCurve x 0 u) < ν := by
  by_cases hsmall : ∀ i : Fin 3, wallValue i x < ν
  · refine ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩
    simpa only [normalizedMaxCurve_initial] using hsmall
  push Not at hsmall
  obtain ⟨i, hi⟩ := hsmall
  have hframe : ∃ a : Fin 6, axisOrder a 0 = i := by
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  obtain ⟨a, ha⟩ := hframe
  let A := axisFrame a
  have hcA : stateConstraint (A.map x) = 1 := (A.constraint x).trans hc
  have hpA : positiveWalls (A.map x) := (A.positive x).mpr hp
  have hprodA (u : ℝ) (hu : u ∈ Icc 0 (5 / ν ^ 2)) :
      normalizedWallProductsBound Δ (normalizedMaxCurve (A.map x) 0 u) := by
    rw [A.maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hu.1)]
    exact (hprod u hu).axisFrame a
  have hnA : ν ≤ A.map x 2 := by
    change ν ≤ wallValue 0 ((axisFrame a).map x)
    rw [axisFrame_wallValue, ha]
    exact hi
  obtain ⟨u, hu, hall⟩ := exists_smallWall_entry_from_first_wall hcA hpA hν hνmax hΔ hnA hprodA
  refine ⟨u, hu, ?_⟩
  intro j
  obtain ⟨k, hk⟩ := (axisOrder_bijective a).surjective j
  have HH := hall k
  rw [A.maxCurve (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hu.1)] at HH
  simpa only [A, axisFrame_wallValue, hk] using HH

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


/-- Any uniformly Taub-avoiding orbit with sufficiently small future wall products reaches a transverse fixed-height entrance. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ ν₀ > (0 : ℝ), ν₀ ≤ 1 / 4 ∧ ∃ c > (0 : ℝ), c ≤ 1 ∧
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ → ∀ Δ : ℝ, 0 ≤ Δ → Δ ≤ ν / 8 →
        ∀ x : NormalizedState, stateConstraint x = 1 → positiveWalls x →
          normalizedTaubAvoidance ε x →
          (∀ u ≥ (0 : ℝ), normalizedWallProductsBound Δ (normalizedMaxCurve x 0 u)) →
          ∃ s ∈ Icc 0 (5 / ν ^ 2), ∃ T > s, ∃ i : Fin 3,
            (∀ j : Fin 3, wallValue j (normalizedMaxCurve x 0 s) < ν) ∧
            IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧
              ∃ j : Fin 3, wallValue j (normalizedMaxCurve x 0 t) = ν} T ∧
            (∀ u ∈ Ico s T, ∀ j : Fin 3, wallValue j (normalizedMaxCurve x 0 u) < ν) ∧
            wallValue i (normalizedMaxCurve x 0 T) = ν ∧
            (∀ j : Fin 3, j ≠ i → wallValue j (normalizedMaxCurve x 0 T) < ν) ∧
            c ≤ wallRate i (normalizedMaxCurve x 0 T) ∧
            HasDerivAt (fun u => wallValue i (normalizedMaxCurve x 0 u))
              (wallRate i (normalizedMaxCurve x 0 T) * ν) T ∧
            0 < c * ν ∧ c * ν ≤ wallRate i (normalizedMaxCurve x 0 T) * ν := by
  obtain ⟨ν₀, hν₀, hν₀max, c, hc, hcmax, H⟩ := exists_smallWall_first_upcrossing hε
  refine ⟨ν₀, hν₀, hν₀max, c, hc, hcmax, ?_⟩
  intro ν hν hνcap Δ hΔ hΔmax x hx hp ha hprod
  obtain ⟨s, hs, hsmall⟩ := exists_normalized_smallWall_entry hx hp hν (hνcap.trans hν₀max)
    ⟨hΔ, hΔmax⟩ (fun u hu => hprod u hu.1)
  let y := normalizedMaxCurve x 0 s
  have hdoms := normalizedMaxDomain_contains_Ici_of_constraint hx 0 hs.1
  have hy : stateConstraint y = 1 := (normalizedMaxCurve_forward_of_constraint hx hs.1).2.1
  have hpos : positiveWalls y := normalized_positive_walls_invariant
    (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun v hv => hasDerivAt_normalizedMaxCurve hv) (initial_mem_normalizedMaxDomain x 0) hdoms
    (by simpa only [normalizedMaxCurve_initial] using hp)
  obtain ⟨τ, hτ, i, hfirst, hpre, hgap, hhit, hother, _, _, _⟩ :=
    H ν hν hνcap y hy hpos hsmall (ha.forward hs.1 hdoms)
  have hrestart (u : ℝ) (hu : s ≤ u) :
      normalizedMaxCurve x 0 u = normalizedMaxCurve y 0 (u - s) :=
    (normalizedMaxCurve_restart hdoms
      (normalizedMaxDomain_contains_Ici_of_constraint hy 0 (sub_nonneg.mpr hu))).2
  have hend : normalizedMaxCurve x 0 (s + τ) = normalizedMaxCurve y 0 τ := by
    simpa only [add_sub_cancel_left] using hrestart (s + τ) (by linarith only [hτ])
  have hT : s < s + τ := by linarith only [hτ]
  have hTdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 (hs.1.trans hT.le)
  have hactive : wallValue i (normalizedMaxCurve x 0 (s + τ)) = ν := by rw [hend]; exact hhit
  have hleast : IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain x 0 ∧
      ∃ j : Fin 3, wallValue j (normalizedMaxCurve x 0 t) = ν} (s + τ) := by
    refine ⟨⟨hT, hTdom, i, hactive⟩, ?_⟩
    intro u hu
    have hud : u - s ∈ normalizedMaxDomain y 0 :=
      normalizedMaxDomain_contains_Ici_of_constraint hy 0 (sub_pos.mpr hu.1).le
    have hh : ∃ j : Fin 3, wallValue j (normalizedMaxCurve y 0 (u - s)) = ν := by
      rw [← hrestart u hu.1.le]
      exact hu.2.2
    have hle := hfirst.2 ⟨sub_pos.mpr hu.1, hud, hh⟩
    linarith only [hle]
  have hprefix (u : ℝ) (hu : u ∈ Ico s (s + τ)) (j : Fin 3) :
      wallValue j (normalizedMaxCurve x 0 u) < ν := by
    rw [hrestart u hu.1]
    exact hpre (u - s) ⟨sub_nonneg.mpr hu.1, by linarith only [hu.2]⟩ j
  have hother' (j : Fin 3) (hj : j ≠ i) : wallValue j (normalizedMaxCurve x 0 (s + τ)) < ν := by
    rw [hend]
    exact hother j hj
  have hrate : c ≤ wallRate i (normalizedMaxCurve x 0 (s + τ)) := by
    rw [hend]
    exact (hgap τ ⟨hτ.le, le_rfl⟩).1
  have hd := hasDerivAt_wallValue
    (normalizedMaxCurve_forward_of_constraint hx (hs.1.trans hT.le)).1 i
  rw [hactive] at hd
  exact ⟨s, hs, s + τ, hT, i, hsmall, hleast, hprefix, hactive, hother', hrate, hd,
    mul_pos hc hν, mul_le_mul_of_nonneg_right hrate hν.le⟩
