-- Prove2me | solution 1 for BianchiIX.exists_compact_tail_state_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:09:59.395465+00:00
-- url     : https://prove2.me/submissions/14c44d01-3871-4801-bb51-c727cadf266d

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_coreTail_reference_regular
import Theorems.Thm_BianchiIX_exists_compact_connection_tail
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

noncomputable section
open BianchiIX
open Set


/-- The uniform finite-tail derivative bound controls every signed wall perturbation. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧ ContDiffAt ℝ 2 (coreTailState η) Y ∧
        ‖coreTailState η Y - (![1 - Real.sqrt (Y 0 ^ 2 - η ^ 2), 0, η, 0] : ProjectiveState)‖ ≤
          C * (|Y 1| + |Y 2|) := by
  obtain ⟨ε, hε, C, hC, Htail⟩ := exists_compact_connection_tail hη
  let S : Set CoreAngleState := Icc (![31 / 8, -ε, -ε] : CoreAngleState) ![6, ε, ε]
  have hcoords {Y : CoreAngleState} (hY : Y ∈ S) :
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) ∧ |Y 1| ≤ ε ∧ |Y 2| ≤ ε :=
    ⟨⟨hY.1 0, hY.2 0⟩, abs_le.mpr ⟨hY.1 1, hY.2 1⟩, abs_le.mpr ⟨hY.1 2, hY.2 2⟩⟩
  have hdiff (Y : CoreAngleState) (hY : Y ∈ S) : DifferentiableAt ℝ (coreTailState η) Y :=
    (Htail Y (hcoords hY).1 (hcoords hY).2.1 (hcoords hY).2.2).2.2.1.differentiableAt (by norm_num)
  have hbound (Y : CoreAngleState) (hY : Y ∈ S) : ‖fderiv ℝ (coreTailState η) Y‖ ≤ C := by
    have H := (Htail Y (hcoords hY).1 (hcoords hY).2.1 (hcoords hY).2.2).2.2.2
    linarith only [H, abs_nonneg (coreTailTime η Y), norm_nonneg (coreTailState η Y),
      norm_nonneg (fderiv ℝ (coreTailTime η) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (coreTailTime η)) Y),
      norm_nonneg (fderiv ℝ (fderiv ℝ (coreTailState η)) Y)]
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  have hY : Y ∈ S := by
    constructor
    · intro i
      fin_cases i
      · exact hk.1
      · exact (abs_le.mp hu).1
      · exact (abs_le.mp hw).1
    · intro i
      fin_cases i
      · exact hk.2
      · exact (abs_le.mp hu).2
      · exact (abs_le.mp hw).2
  have hbase : (![Y 0, 0, 0] : CoreAngleState) ∈ S := by
    constructor
    · intro i
      fin_cases i
      · exact hk.1
      · exact neg_nonpos.mpr hε.le
      · exact neg_nonpos.mpr hε.le
    · intro i
      fin_cases i
      · exact hk.2
      · exact hε.le
      · exact hε.le
  have H := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound (convex_Icc _ _) hbase hY
  have hnorm : ‖Y - (![Y 0, 0, 0] : CoreAngleState)‖ ≤ |Y 1| + |Y 2| := by
    apply (pi_norm_le_iff_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr
    intro i
    fin_cases i
    · change |Y 0 - Y 0| ≤ |Y 1| + |Y 2|
      rw [sub_self, abs_zero]
      exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    · change |Y 1 - 0| ≤ |Y 1| + |Y 2|
      rw [sub_zero]
      exact le_add_of_nonneg_right (abs_nonneg (Y 2))
    · change |Y 2 - 0| ≤ |Y 1| + |Y 2|
      rw [sub_zero]
      exact le_add_of_nonneg_left (abs_nonneg (Y 1))
  have href := (coreTail_reference_regular (k := Y 0) (by linarith only [hk.1])
    ⟨hη.1, by linarith only [hη.2]⟩).2.1
  rw [href] at H
  have HY := Htail Y hk hu hw
  exact ⟨HY.1, HY.2.1, HY.2.2.1, H.trans (mul_le_mul_of_nonneg_left hnorm hC.le)⟩
