-- Prove2me | solution 1 for BianchiIX.exists_compact_tail_entrance
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T08:07:30.082499+00:00
-- url     : https://prove2.me/submissions/1b7d35a4-f33c-40cf-9b08-abc34e31181c

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreTailPerturbation
import Theorems.Thm_BianchiIX_compact_connection_boundary_radius_bounds
import Theorems.Thm_BianchiIX_exists_compact_tail_multiplier_bounds
import Theorems.Thm_BianchiIX_exists_compact_tail_phase_perturbation
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

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.compact_connection_perturbed_radius_range {K η r : ℝ}
    (hK : 31 / 8 ≤ K ∧ K ≤ 6) (hη : 0 < η ∧ η ≤ 1 / 8)
    (herr : |r - (Real.sqrt (K ^ 2 - η ^ 2) - 2)| ≤ η ^ 2 / 24) :
    7 / 4 ≤ r ∧ r ≤ 4 - η ^ 2 / 24 ∧ r < 4 := by
  have H := compact_connection_boundary_radius_bounds hK hη
  have hηsq := pow_le_pow_left₀ hη.1.le hη.2 2
  have hlo := (abs_le.mp herr).1
  have hhi := (abs_le.mp herr).2
  have hu : r ≤ 4 - η ^ 2 / 24 := by linarith only [H.2, hhi]
  exact ⟨by nlinarith only [H.1, hlo, hηsq], hu,
    lt_of_le_of_lt hu (by nlinarith only [sq_pos_of_pos hη.1])⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_coreTailReflectedRadius (n : WithTop ℕ∞) {η : ℝ} {Y : CoreAngleState}
    (hP : ContDiffAt ℝ n (coreTailState η) Y) (hm : 1 < -coreTailState η Y 0) :
    ContDiffAt ℝ n (coreTailReflectedRadius η) Y := by
  have ha : ContDiffAt ℝ n (fun Z => -coreTailState η Z 0 - 1) Y :=
    (contDiffAt_pi.mp hP 0).neg.sub contDiffAt_const
  have hb : ContDiffAt ℝ n (fun Z => coreTailState η Z 3) Y := contDiffAt_pi.mp hP 3
  have hsq : (-coreTailState η Y 0 - 1) ^ 2 + coreTailState η Y 3 ^ 2 ≠ 0 := by
    have hp : 0 < -coreTailState η Y 0 - 1 := by linarith only [hm]
    exact ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hp) (sq_nonneg _))
  exact ((ha.pow 2).add (hb.pow 2)).sqrt hsq

end
end

/-- One signed wall neighborhood gives B.45, B.46, the correct reflected branch, and the entrance phase range. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 8) :
    ∃ ε > (0 : ℝ), ∃ C > (0 : ℝ), ∀ Y : CoreAngleState,
      (31 / 8 ≤ Y 0 ∧ Y 0 ≤ 6) → |Y 1| ≤ ε → |Y 2| ≤ ε →
      coreTailValid η Y ∧ ContDiffAt ℝ 2 (coreTailTime η) Y ∧
        ContDiffAt ℝ 2 (coreTailState η) Y ∧ ContDiffAt ℝ 2 (coreTailReflectedRadius η) Y ∧
        7 / 4 ≤ -coreTailState η Y 0 - 1 ∧
        (7 / 4 ≤ coreTailReflectedRadius η Y ∧
          coreTailReflectedRadius η Y ≤ 4 - η ^ 2 / 24 ∧ coreTailReflectedRadius η Y < 4) ∧
        |coreTailReflectedRadius η Y - (Real.sqrt (Y 0 ^ 2 - η ^ 2) - 2)| ≤ C * (|Y 1| + |Y 2|) ∧
        C * (|Y 1| + |Y 2|) ≤ η ^ 2 / 24 ∧
        projectiveReflection (coreTailState η Y) =
          ![-coreTailState η Y 0, Y 1 * coreTailMultiplier η Y 0, Y 2 * coreTailMultiplier η Y 1, η] ∧
        ∀ i : Fin 2, 0 < coreTailMultiplier η Y i ∧
          ContDiffAt ℝ 2 (fun Z => coreTailMultiplier η Z i) Y ∧
          ContDiffAt ℝ 2 (fun Z => Real.log (coreTailMultiplier η Z i)) Y ∧
          coreTailMultiplier η Y i + (coreTailMultiplier η Y i)⁻¹ +
            ‖fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i)) Y‖ +
            ‖fderiv ℝ (fderiv ℝ (fun Z => Real.log (coreTailMultiplier η Z i))) Y‖ ≤ C := by
  obtain ⟨εp, hεp, Cp, hCp, Hp⟩ := exists_compact_tail_phase_perturbation hη
  obtain ⟨εm, hεm, Cm, hCm, Hm⟩ := exists_compact_tail_multiplier_bounds hη
  let C := max Cp Cm
  have hC : 0 < C := lt_of_lt_of_le hCp (le_max_left _ _)
  let ε := min εp (min εm (η ^ 2 / (48 * C)))
  have hε : 0 < ε := lt_min hεp (lt_min hεm
    (div_pos (sq_pos_of_pos hη.1) (mul_pos (by norm_num) hC)))
  have hεp' : ε ≤ εp := min_le_left _ _
  have hεm' : ε ≤ εm := (min_le_right _ _).trans (min_le_left _ _)
  have hεb : ε ≤ η ^ 2 / (48 * C) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ε, hε, C, hC, ?_⟩
  intro Y hk hu hw
  have Hphase := Hp Y hk (hu.trans hεp') (hw.trans hεp')
  have Hmult := Hm Y hk (hu.trans hεm') (hw.trans hεm')
  have hbudget : C * (|Y 1| + |Y 2|) ≤ η ^ 2 / 24 := by
    have H := (le_div_iff₀ (by positivity : 0 < 48 * C)).mp hεb
    nlinarith only [H, mul_le_mul_of_nonneg_left (add_le_add hu hw) hC.le]
  have henlarge : Cp * (|Y 1| + |Y 2|) ≤ C * (|Y 1| + |Y 2|) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have hphase := Hphase.2.2.2.1.trans henlarge
  have hbranch := Hphase.2.2.2.2.trans (henlarge.trans hbudget)
  have hrange := compact_connection_perturbed_radius_range hk hη (hphase.trans hbudget)
  have hm : 7 / 4 ≤ -coreTailState η Y 0 - 1 :=
    (compact_connection_perturbed_radius_range hk hη hbranch).1
  refine ⟨Hphase.1, Hphase.2.1, Hphase.2.2.1,
    contDiffAt_coreTailReflectedRadius 2 Hphase.2.2.1 (by linarith only [hm]),
    hm, hrange, hphase, hbudget, Hmult.2.2.2.1, ?_⟩
  intro i
  have Hi := Hmult.2.2.2.2 i
  exact ⟨Hi.1, Hi.2.1, Hi.2.2.1, Hi.2.2.2.trans (le_max_right _ _)⟩
