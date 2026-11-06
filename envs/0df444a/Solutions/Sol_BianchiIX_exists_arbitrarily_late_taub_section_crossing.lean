-- Prove2me | solution 1 for BianchiIX.exists_arbitrarily_late_taub_section_crossing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:08:06.81622+00:00
-- url     : https://prove2.me/submissions/9a4430c2-0e77-4514-938e-384a7b0bfc24

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_GeometricExceptionData
import Definitions.Def_BianchiIX_Dynamics_FlowComposition
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxDomain
import Theorems.Thm_BianchiIX_exists_deep_taub_crossing
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.taubRadiusSq_nonneg (s b c : ℝ) : 0 ≤ taubRadiusSq s b c :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_rebase {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀) :
    normalizedMaxCurve (normalizedMaxCurve x t₀ s) s t = normalizedMaxCurve x t₀ t :=
  normalizedMaxCurve_eqOn ((maximalNormalizedSolution x t₀).rebase hs) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.mainWallChart_coordinates {h : ℝ} {x : NormalizedState}
    (hpos : positiveWalls x) (hcon : stateConstraint x = 1) (hp : x 0 < 0) (hh : x 2 = h) :
    mainWallCoordinates x ∈ mainWallChartDomain h ∧ mainWallChart h (mainWallCoordinates x) = x := by
  have hr : mainWallRadicand h (mainWallCoordinates x) = x 0 ^ 2 := by
    change 1 - x 1 ^ 2 - curvature h (Real.exp (- -Real.log (x 3)))
      (Real.exp (- -Real.log (x 4))) = x 0 ^ 2
    rw [neg_neg, neg_neg, Real.exp_log hpos.2.1, Real.exp_log hpos.2.2]
    have H : x 0 ^ 2 + x 1 ^ 2 + curvature h (x 3) (x 4) = 1 := by
      simpa only [stateConstraint, constraint, shearSq, hh] using hcon
    linarith
  refine ⟨by change 0 < mainWallRadicand h (mainWallCoordinates x)
             rw [hr]; exact sq_pos_of_ne_zero (ne_of_lt hp), ?_⟩
  ext i
  fin_cases i
  · change -Real.sqrt (mainWallRadicand h (mainWallCoordinates x)) = x 0
    rw [hr, Real.sqrt_sq_eq_abs, abs_of_neg hp, neg_neg]
  · rfl
  · exact hh.symm
  · simp [mainWallChart, mainWallCoordinates, Real.exp_log hpos.2.1]
  · simp [mainWallChart, mainWallCoordinates, Real.exp_log hpos.2.2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.NormalizedSymmetry.fixed_maxCurve_iff (A : NormalizedSymmetry)
    {x : NormalizedState} {t₀ t : ℝ} (ht : t ∈ normalizedMaxDomain x t₀) :
    A.map (normalizedMaxCurve x t₀ t) = normalizedMaxCurve x t₀ t ↔ A.map x = x := by
  constructor
  · intro heq
    have hAt : t ∈ normalizedMaxDomain (A.map x) t₀ := by rwa [A.maxDomain]
    calc
      A.map x = normalizedMaxCurve (normalizedMaxCurve (A.map x) t₀ t) t t₀ := by
        rw [normalizedMaxCurve_rebase hAt (initial_mem_normalizedMaxDomain _ _), normalizedMaxCurve_initial]
      _ = normalizedMaxCurve (normalizedMaxCurve x t₀ t) t t₀ := by rw [A.maxCurve ht, heq]
      _ = x := by rw [normalizedMaxCurve_rebase ht (initial_mem_normalizedMaxDomain _ _), normalizedMaxCurve_initial]
  · intro heq
    rw [← A.maxCurve ht, heq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubRadiusSq_eq_zero_iff (x : NormalizedState) :
    normalizedTaubRadiusSq x = 0 ↔ axisSwap x = x := by
  constructor
  · intro hr
    dsimp [normalizedTaubRadiusSq, taubRadiusSq] at hr
    have hs : x 1 = 0 := by nlinarith [sq_nonneg (x 3 - x 4)]
    have hw : x 3 = x 4 := by nlinarith [sq_nonneg (x 1)]
    ext i
    fin_cases i <;> simp [axisSwap, hs, hw]
  · intro heq
    have hs := congrFun heq 1
    have hw := congrFun heq 3
    change -x 1 = x 1 at hs
    change x 4 = x 3 at hw
    dsimp [normalizedTaubRadiusSq, taubRadiusSq]
    rw [hw]
    nlinarith only [hs]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedTaubRadiusSq_maxCurve_pos {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) (hr : 0 < normalizedTaubRadiusSq x) :
    0 < normalizedTaubRadiusSq (normalizedMaxCurve x t₀ t) := by
  apply lt_of_le_of_ne (taubRadiusSq_nonneg _ _ _)
  intro heq
  have hf := (normalizedTaubRadiusSq_eq_zero_iff _).mp heq.symm
  have hi := (NormalizedSymmetry.swap.fixed_maxCurve_iff ht).mp hf
  exact (ne_of_gt hr) ((normalizedTaubRadiusSq_eq_zero_iff _).mpr hi)

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
open Set

private theorem BianchiIX.normalizedTaubDistance_sq (x : NormalizedState) :
    normalizedEuclideanDistance x (taubPoint 0) ^ 2 =
      (1 + x 0) ^ 2 + normalizedTaubRadiusSq x + x 2 ^ 2 + 2 * x 3 * x 4 := by
  rw [normalizedEuclideanDistance_sq]
  simp [taubPoint, Fin.sum_univ_succ, normalizedTaubRadiusSq, taubRadiusSq]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.eventually_normalizedWallProductsBound {x : NormalizedState}
    (H : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ∀ᶠ t in atTop, normalizedWallProductsBound Δ (normalizedMaxCurve x 0 t) := by
  have hcut : 0 < Δ ^ 2 / 4 := by positivity
  filter_upwards [(H 0 1 (by decide)).eventually (gt_mem_nhds hcut),
    (H 1 2 (by decide)).eventually (gt_mem_nhds hcut),
    (H 2 0 (by decide)).eventually (gt_mem_nhds hcut)] with t h01 h12 h20
  change normalizedMaxCurve x 0 t 2 * normalizedMaxCurve x 0 t 3 < Δ ^ 2 / 4 at h01
  change normalizedMaxCurve x 0 t 3 * normalizedMaxCurve x 0 t 4 < Δ ^ 2 / 4 at h12
  change normalizedMaxCurve x 0 t 4 * normalizedMaxCurve x 0 t 2 < Δ ^ 2 / 4 at h20
  exact ⟨by nlinarith only [h01], by nlinarith only [h12], by nlinarith only [h20]⟩

end
end


/-- Arbitrarily late approach to one Taub point forces arbitrarily late crossings of the same fixed main-wall section. -/
theorem solution {x : NormalizedState} {h d : ℝ}
    (hc : stateConstraint x = 1) (hp : positiveWalls x) (hr : 0 < normalizedTaubRadiusSq x)
    (hh : 0 < h) (hhmax : h ≤ 1 / 16) (hd : 0 < d) (hdh : d < h / 8)
    (hprod : ∀ i j : Fin 3, i ≠ j → Tendsto
      (fun t => wallValue i (normalizedMaxCurve x 0 t) * wallValue j (normalizedMaxCurve x 0 t)) atTop (𝓝 0))
    (hvisit : ∀ ε > (0 : ℝ), ∀ R : ℝ, ∃ t ≥ R,
      normalizedEuclideanDistance (normalizedMaxCurve x 0 t) (taubPoint 0) < ε) :
    ∀ R : ℝ, ∀ η > (0 : ℝ), ∃ c > max R 0, c ∈ normalizedMaxDomain x 0 ∧
      ∃ y ∈ mainWallChartDomain h, mainWallChart h y = normalizedMaxCurve x 0 c ∧
        |y 0| < d ∧ Real.exp (-y 1) < d ∧ Real.exp (-y 2) < d ∧
        normalizedTaubRadiusSq (normalizedMaxCurve x 0 c) < η ∧
        normalizedField (normalizedMaxCurve x 0 c) 2 ≤ -5 * h / 4 := by
  intro R η hη
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_normalizedWallProductsBound hprod
    (div_pos hd (by norm_num) : 0 < d / 4))
  let a := max (max R 0) T + 1
  have haR : max R 0 < a := by dsimp [a]; linarith only [le_max_left (max R 0) T]
  have ha0 : 0 ≤ a := (le_max_right R 0).trans haR.le
  have haT : T ≤ a := by dsimp [a]; linarith only [le_max_right (max R 0) T]
  have hRa : 0 < normalizedTaubRadiusSq (normalizedMaxCurve x 0 a) :=
    normalizedTaubRadiusSq_maxCurve_pos (normalizedMaxDomain_contains_Ici hp hc 0 ha0) hr
  let ε := min (min (d / 8) (Real.sqrt (normalizedTaubRadiusSq (normalizedMaxCurve x 0 a)) / 4))
    (Real.sqrt η / 4)
  have hε : 0 < ε := lt_min (lt_min (by positivity) (div_pos (Real.sqrt_pos.mpr hRa) (by norm_num)))
    (div_pos (Real.sqrt_pos.mpr hη) (by norm_num))
  have hεd : ε ≤ d / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hεr : ε ≤ Real.sqrt (normalizedTaubRadiusSq (normalizedMaxCurve x 0 a)) / 4 :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hεη : ε ≤ Real.sqrt η / 4 := min_le_right _ _
  have hεr2 := pow_le_pow_left₀ hε.le hεr 2
  have hεη2 := pow_le_pow_left₀ hε.le hεη 2
  have hstart : 4 * ε ^ 2 < normalizedTaubRadiusSq (normalizedMaxCurve x 0 a) := by
    nlinarith only [hεr2, Real.sq_sqrt hRa.le, hRa]
  have hsmall : 2 * ε ^ 2 < η := by nlinarith only [hεη2, Real.sq_sqrt hη.le, hη]
  obtain ⟨b, hb, hbdist⟩ := hvisit ε hε (a + 1)
  have hab : a < b := by linarith only [hb]
  have hphysical (t : ℝ) (ht : t ∈ Icc a b) := normalizedMaxCurve_forward hp hc (ha0.trans ht.1)
  obtain ⟨c, hcint, hnc, hpc, hsc, huc, hwc, hrc, hspeed⟩ := exists_deep_taub_crossing hab
    hh hhmax hd hdh hε (by linarith only [hεd, hd])
    (fun t ht => (hphysical t ht).1) (fun t ht => (hphysical t ht).2.2.1)
    (fun t ht => (hphysical t ht).2.1) (fun t ht => hT t (haT.trans ht.1)) hstart hbdist.le
  have hctime : 0 ≤ c := ha0.trans hcint.1.le
  have hcp := normalizedMaxCurve_forward hp hc hctime
  obtain ⟨hy, hchart⟩ := mainWallChart_coordinates hcp.2.1 hcp.2.2.1
    (by linarith only [hpc]) hnc
  refine ⟨c, haR.trans hcint.1, normalizedMaxDomain_contains_Ici hp hc 0 hctime,
    mainWallCoordinates (normalizedMaxCurve x 0 c), hy, hchart, hsc, ?_, ?_, ?_, hspeed⟩
  · simpa [mainWallCoordinates, Real.exp_log hcp.2.1.2.1] using huc
  · simpa [mainWallCoordinates, Real.exp_log hcp.2.1.2.2] using hwc
  · have hdist := pow_le_pow_left₀ (normalizedEuclideanDistance_nonneg _ _) hbdist.le 2
    rw [normalizedTaubDistance_sq] at hdist
    have H := mul_nonneg (hphysical b ⟨hab.le, le_rfl⟩).2.1.2.1.le
      (hphysical b ⟨hab.le, le_rfl⟩).2.1.2.2.le
    nlinarith only [hrc, hsmall, hdist, H, sq_nonneg (1 + normalizedMaxCurve x 0 b 0),
      sq_nonneg (normalizedMaxCurve x 0 b 2)]
