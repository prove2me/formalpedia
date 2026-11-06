-- Prove2me | solution 1 for BianchiIX.exists_compact_connection_entrance_data
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:10:54.578092+00:00
-- url     : https://prove2.me/submissions/44d94348-7c86-4a72-a96a-f3ff478832fe

import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreTailPerturbation
import Definitions.Def_BianchiIX_Dynamics_CompactConnectionReturn
import Theorems.Thm_BianchiIX_exists_compact_tail_entrance
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


/-- The finite tail can be made to satisfy any prescribed common entrance amplitude bound. -/
theorem solution {δ η : ℝ}
    (hδ : 0 < δ ∧ δ ≤ 1 / 10000) (hη : 0 < η ∧ η ≤ δ) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → (0 < Y 1 ∧ Y 1 ≤ ε) → (0 < Y 2 ∧ Y 2 ≤ ε) →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (compactConnectionEntry η) Y ∧
        (7 / 4 ≤ coreRadius (compactConnectionEntry η Y 0) (compactConnectionEntry η Y 2) ∧
          coreRadius (compactConnectionEntry η Y 0) (compactConnectionEntry η Y 2) < 4) ∧
        1 ≤ compactConnectionEntry η Y 0 ∧
        (0 < compactConnectionEntry η Y 1 ∧ compactConnectionEntry η Y 1 ≤ δ) ∧
        (0 < compactConnectionEntry η Y 2 ∧ compactConnectionEntry η Y 2 ≤ 1 / 2) ∧
        compactConnectionEntry η Y 3 = η ∧
        compactConnectionEntry η Y 1 ≤ C * Y 1 ∧ compactConnectionEntry η Y 2 ≤ C * Y 2 := by
  obtain ⟨ε₀, hε₀, C, hC, HC⟩ := exists_compact_tail_entrance
    ⟨hη.1, by linarith [hη.2, hδ.2]⟩
  let ε := min ε₀ (min (δ / C) (1 / (2 * C)))
  have hε : 0 < ε := lt_min hε₀ (lt_min (div_pos hδ.1 hC) (by positivity))
  have hε₀' : ε ≤ ε₀ := min_le_left _ _
  have hεδ : ε * C ≤ δ := (le_div_iff₀ hC).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hεv : ε * C ≤ 1 / 2 := by
    have H := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
      (show ε ≤ 1 / (2 * C) from (min_le_right _ _).trans (min_le_right _ _))
    nlinarith only [H]
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  obtain ⟨htail, htime, hstate, _, hm, hrange, _, _, hform, hmult⟩ :=
    HC Y hk (by rw [abs_of_pos hu.1]; exact hu.2.trans hε₀')
      (by rw [abs_of_pos hw.1]; exact hw.2.trans hε₀')
  have hbound (i : Fin 2) : coreTailMultiplier η Y i ≤ C := by
    have H := (hmult i).2.2.2
    have hBi := (hmult i).1
    linarith only [H, inv_nonneg.mpr hBi.le,
      norm_nonneg (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y)]
  have hentry : ContDiffAt ℝ 2 (compactConnectionEntry η) Y := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · exact (contDiffAt_pi.mp hstate 0).neg
    · exact contDiffAt_pi.mp hstate 1
    · exact contDiffAt_pi.mp hstate 3
    · exact contDiffAt_pi.mp hstate 2
  have hU : compactConnectionEntry η Y 1 = Y 1 * coreTailMultiplier η Y 0 :=
    congrFun hform 1
  have hV : compactConnectionEntry η Y 2 = Y 2 * coreTailMultiplier η Y 1 :=
    congrFun hform 2
  have hUc : compactConnectionEntry η Y 1 ≤ C * Y 1 := by
    rw [hU, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbound 0) hu.1.le
  have hVc : compactConnectionEntry η Y 2 ≤ C * Y 2 := by
    rw [hV, mul_comm C]
    exact mul_le_mul_of_nonneg_left (hbound 1) hw.1.le
  refine ⟨htail, htime, hentry, ⟨hrange.1, hrange.2.2⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    congrFun hform 3, hUc, hVc⟩
  · change 1 ≤ -coreTailState η Y 0
    linarith only [hm]
  · rw [hU]; exact mul_pos hu.1 (hmult 0).1
  · exact hUc.trans ((mul_le_mul_of_nonneg_left hu.2 hC.le).trans (by simpa only [mul_comm] using hεδ))
  · rw [hV]; exact mul_pos hw.1 (hmult 1).1
  · exact hVc.trans ((mul_le_mul_of_nonneg_left hw.2 hC.le).trans (by simpa only [mul_comm] using hεv))
