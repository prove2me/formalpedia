-- Prove2me | solution 1 for BianchiIX.exists_compact_tail_phase_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:04:06.659028+00:00
-- url     : https://prove2.me/submissions/d8fe6403-1daa-4231-9962-3530422daa92

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_CoreTailPerturbation
import Theorems.Thm_BianchiIX_compact_connection_boundary_radius_bounds
import Theorems.Thm_BianchiIX_exists_compact_tail_state_perturbation
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

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_le_abs_add (a b : ℝ) : phaseNorm a b ≤ |a| + |b| := by
  have hr : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hs := phaseNorm_sq a b
  nlinarith only [hr, hs, sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b,
    mul_nonneg (abs_nonneg a) (abs_nonneg b)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_boundary_error {a b c : ℝ} (hc : 0 ≤ c) :
    |phaseNorm a b - c| ≤ |a - c| + |b| := by
  have hr : 0 ≤ phaseNorm a b := Real.sqrt_nonneg _
  have hrad : a ≤ phaseNorm a b := by nlinarith only [phaseNorm_sq a b, hr, sq_nonneg b]
  have ha : |a| ≤ |a - c| + c := by
    have H := abs_add_le (a - c) c
    simpa only [sub_add_cancel, abs_of_nonneg hc] using H
  apply abs_le.mpr
  constructor
  · linarith only [hrad, neg_abs_le (a - c), abs_nonneg b]
  · linarith only [phaseNorm_le_abs_add a b, ha]

end
end

private theorem BianchiIX.coreTailReflectedRadius_eq (η : ℝ) (Y : CoreAngleState) :
    coreTailReflectedRadius η Y = phaseNorm (-coreTailState η Y 0 - 1) (coreTailState η Y 3) := rfl

/-- B.46 for the actual nonzero-wall tail, together with the state error controlling its branch. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧ ContDiffAt ℝ 2 (coreTailState η) Y ∧
        |coreTailReflectedRadius η Y - (Real.sqrt (Y 0 ^ 2 - η ^ 2) - 2)| ≤ C * (|Y 1| + |Y 2|) ∧
        |(-coreTailState η Y 0 - 1) - (Real.sqrt (Y 0 ^ 2 - η ^ 2) - 2)| ≤ C * (|Y 1| + |Y 2|) := by
  obtain ⟨ε, hε, C, hC, Htail⟩ := exists_compact_tail_state_perturbation hη
  refine ⟨ε, hε, 2 * C, by positivity, ?_⟩
  intro Y hk hu hw
  have HY := Htail Y hk hu hw
  let s := Real.sqrt (Y 0 ^ 2 - η ^ 2) - 2
  have hs : 0 ≤ s := by
    have H := (compact_connection_boundary_radius_bounds hk hη).1
    have hηsq := pow_le_pow_left₀ hη.1.le hη.2 2
    dsimp only [s]
    nlinarith only [H, hηsq]
  have hcoord (i : Fin 4) := (norm_le_pi_norm
    (coreTailState η Y - (![1 - Real.sqrt (Y 0 ^ 2 - η ^ 2), 0, η, 0] : ProjectiveState)) i).trans HY.2.2.2
  have hm : |(-coreTailState η Y 0 - 1) - s| ≤ C * (|Y 1| + |Y 2|) := by
    have heq : (-coreTailState η Y 0 - 1) - s =
        -(coreTailState η Y 0 - (1 - Real.sqrt (Y 0 ^ 2 - η ^ 2))) := by dsimp only [s]; ring
    rw [heq, abs_neg]
    exact hcoord 0
  have hwout : |coreTailState η Y 3| ≤ C * (|Y 1| + |Y 2|) := by simpa using hcoord 3
  have hphase := phaseNorm_boundary_error (a := -coreTailState η Y 0 - 1)
    (b := coreTailState η Y 3) hs
  refine ⟨HY.1, HY.2.1, HY.2.2.1, ?_, ?_⟩
  · rw [coreTailReflectedRadius_eq]
    change |phaseNorm (-coreTailState η Y 0 - 1) (coreTailState η Y 3) - s| ≤ _
    linarith only [hphase, hm, hwout]
  · exact hm.trans (by nlinarith only [mul_nonneg hC.le (add_nonneg (abs_nonneg (Y 1)) (abs_nonneg (Y 2)))])
