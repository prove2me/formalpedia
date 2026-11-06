-- Prove2me | solution 1 for BianchiIX.exists_terminal_axisCycle_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T18:07:20.898797+00:00
-- url     : https://prove2.me/submissions/cf83d3f6-06a7-4da7-9a47-efaf39c1a065

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
import Theorems.Thm_BianchiIX_exists_terminal_coreTail_valid
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_fromProjectiveState_toProjectiveState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_projectiveDenom_of_constraint
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_of_coreRadius {m v : ℝ} (hm : m < 1) :
    exitTailGap (coreRadius m v) v = 1 - m := by
  unfold exitTailGap
  rw [coreRadius_sq]
  dsimp only [coreEnergy]
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hm] : m - 1 < 0)]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycleDenom_projective (m u v w : ℝ) :
    axisCycleDenom m u v w = projectiveDenom m u v w + 2 * m - 2 := by
  unfold axisCycleDenom projectiveDenom
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycleDenom_wall_split (m u v w : ℝ) :
    axisCycleDenom m u v w = (m + 1) ^ 2 + v ^ 2 + (u - w) ^ 2 - 2 * v * (u + w) := by
  unfold axisCycleDenom curvature
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_boundary_denom {R v : ℝ} (hR : 0 < R) (hv : v ^ 2 ≤ R ^ 2) :
    (2 - exitTailGap R v) ^ 2 + v ^ 2 = (R - 2) ^ 2 + 4 * v ^ 2 / (R + exitTailGap R v) := by
  have ht0 : 0 ≤ exitTailGap R v := Real.sqrt_nonneg _
  have hp : R + exitTailGap R v ≠ 0 := (add_pos_of_pos_of_nonneg hR ht0).ne'
  have ht := exitTailGap_sq hv
  field_simp
  nlinarith only [ht, congrArg (fun x => R * x) ht, congrArg (fun x => exitTailGap R v * x) ht]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_denom_split {R v : ℝ} (hR : 0 < R) (hv : v ^ 2 ≤ R ^ 2) (u w : ℝ) :
    axisCycleDenom (1 - exitTailGap R v) u v w =
      (R - 2) ^ 2 + 4 * v ^ 2 / (R + exitTailGap R v) + (u - w) ^ 2 - 2 * v * (u + w) := by
  rw [axisCycleDenom_wall_split]
  have H := exitCycle_boundary_denom hR hv
  nlinarith only [H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycleDenom_wall_error (m u v w : ℝ) :
    |axisCycleDenom m u v w - ((m + 1) ^ 2 + v ^ 2)| ≤
      (|u| + |w|) ^ 2 + 2 * |v| * (|u| + |w|) := by
  rw [axisCycleDenom_wall_split]
  have H := abs_sub ((u - w) ^ 2) (2 * v * (u + w))
  simp only [abs_of_nonneg (sq_nonneg (u - w)), abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at H
  have HS : (u - w) ^ 2 ≤ (|u| + |w|) ^ 2 := by
    have HD := abs_sub u w
    nlinarith only [sq_abs (u - w), (sq_le_sq₀ (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))).mpr HD]
  have HM := mul_le_mul_of_nonneg_left (abs_add_le u w) (by positivity : 0 ≤ 2 * |v|)
  rw [show (m + 1) ^ 2 + v ^ 2 + (u - w) ^ 2 - 2 * v * (u + w) - ((m + 1) ^ 2 + v ^ 2) =
    (u - w) ^ 2 - 2 * v * (u + w) by ring]
  exact H.trans (add_le_add HS HM)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycleDenom_lower {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ 1) :
    39 / 10 * α ^ 2 + 2 / 5 * v ^ 2 < axisCycleDenom (1 - exitTailGap R v) u v w := by
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have hRc := abs_le.mp hR
  have hRlo : 7 / 4 ≤ R := by linarith only [hRc.1, hB, hα.1]
  have hRhi : R ≤ 17 / 4 := by linarith only [hRc.2, hB, hα.2]
  have hR0 : 0 < R := by linarith only [hRlo]
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRlo, hv.1, hv.2]
  have ht := exitTailGap_compact hRlo hv
  have hp : 0 < R + exitTailGap R v := by linarith only [hRlo, ht.1]
  have hp9 : R + exitTailGap R v ≤ 9 := by linarith only [hRhi, ht.2]
  have Hfrac : 4 / 9 * v ^ 2 ≤ 4 * v ^ 2 / (R + exitTailGap R v) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hp9 (sq_nonneg v)]
  have hρ : 199 / 100 * α ≤ R - 2 := by linarith only [hRc.1, hB, hα.1]
  have hρsq : (199 / 100 * α) ^ 2 ≤ (R - 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by linarith only [hρ, hα.1])).mpr hρ
  have hBsq : B ^ 2 ≤ (α / 10000) ^ 2 := (sq_le_sq₀ hB0 (by positivity)).mpr hB
  have hsum : u + w ≤ B := (add_le_add (le_abs_self u) (le_abs_self w)).trans hw
  have hcross := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hv.1)
  have hYoung : 2 * v * B ≤ v ^ 2 / 100 + 100 * B ^ 2 := by nlinarith only [sq_nonneg (v / 10 - 10 * B)]
  rw [exitCycle_denom_split hR0 hvR]
  nlinarith only [Hfrac, hρsq, hBsq, hcross, hYoung, sq_nonneg (u - w), sq_pos_of_pos hα.1, sq_nonneg v]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_newWall_bound {α B H w : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hH : 39 / 10 * α ^ 2 < H) (hw : |w| ≤ B) :
    |4 * w / H| ≤ 2 * B / α ^ 2 := by
  have hH0 : 0 < H := lt_trans (by positivity) hH
  rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_pos hH0]
  apply (div_le_div_iff₀ hH0 (sq_pos_of_pos hα)).mpr
  have HH : 2 * α ^ 2 ≤ H := by nlinarith only [hH, sq_nonneg α]
  nlinarith only [mul_le_mul_of_nonneg_right hw (sq_nonneg α), mul_le_mul_of_nonneg_left HH hB]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_newWall_small {α B H w : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hsmall : B ≤ α ^ 2 / 10000) (hH : 39 / 10 * α ^ 2 < H) (hw : |w| ≤ B) :
    |4 * w / H| ≤ 1 / 5000 := by
  apply (exitCycle_newWall_bound hα hB hH hw).trans
  apply (div_le_iff₀ (sq_pos_of_pos hα)).mpr
  linarith only [hsmall]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycleDenom_terminal_bounds {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    399 / 100 * α ^ 2 < axisCycleDenom (1 - exitTailGap R v) u v w ∧
      axisCycleDenom (1 - exitTailGap R v) u v w < 401 / 100 * α ^ 2 := by
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have hRc := abs_le.mp hR
  have hRlo : 7 / 4 ≤ R := by linarith only [hRc.1, hB, hα.1]
  have hR0 : 0 < R := by linarith only [hRlo]
  have hv1 : v ≤ 1 := by linarith only [hv.2, hα.2]
  have ht := exitTailGap_compact hRlo ⟨hv.1, hv1⟩
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRlo, hv.1, hv1]
  have hp : 0 < R + exitTailGap R v := by linarith only [hRlo, ht.1]
  have hp3 : 3 ≤ R + exitTailGap R v := by linarith only [hRc.1, hB, hα.1, ht.1]
  have Hfrac : 4 * v ^ 2 / (R + exitTailGap R v) ≤ 4 / 3 * v ^ 2 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hp3 (sq_nonneg v)]
  have Hfrac0 : 0 ≤ 4 * v ^ 2 / (R + exitTailGap R v) := by positivity
  have hρlo : 19999 / 10000 * α ≤ R - 2 := by linarith only [hRc.1, hB]
  have hρhi : R - 2 ≤ 20001 / 10000 * α := by linarith only [hRc.2, hB]
  have hρ0 : 0 ≤ R - 2 := by linarith only [hρlo, hα.1]
  have hρsqlo := (sq_le_sq₀ (by positivity) hρ0).mpr hρlo
  have hρsqhi := (sq_le_sq₀ hρ0 (by positivity)).mpr hρhi
  have hvsq := (sq_le_sq₀ hv.1 (by positivity)).mpr hv.2
  have herr := axisCycleDenom_wall_error (1 - exitTailGap R v) u v w
  rw [abs_of_nonneg hv.1] at herr
  have HE : (|u| + |w|) ^ 2 + 2 * v * (|u| + |w|) ≤
      (α / 10000) ^ 2 + 2 * (α / 100) * (α / 10000) := by
    gcongr <;> linarith only [hw, hB, hv.2]
  have Hb := abs_le.mp (herr.trans HE)
  have Hboundary := exitCycle_boundary_denom hR0 hvR
  constructor <;> nlinarith only [Hb.1, Hb.2, Hboundary, Hfrac0, Hfrac, hρsqlo, hρsqhi, hvsq, sq_pos_of_pos hα.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.projectiveCycleDenom_eq (y : ProjectiveState) :
    projectiveCycleDenom y = projectiveStateDenom y + 2 * y 0 - 2 :=
  axisCycleDenom_projective _ _ _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_inverse_clock {y : ProjectiveState} (hD : projectiveStateDenom y ≠ 0) :
    1 + axisCycle (fromProjectiveState y) 0 =
      (6 / projectiveStateDenom y) * projectiveCycleDenom y / 4 := by
  have hr : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  rw [projectiveCycleDenom_eq]
  dsimp only [axisCycle, fromProjectiveState, Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.toProjectiveState_axisCycle_inverse {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) (hH : projectiveCycleDenom y ≠ 0) :
    toProjectiveState (axisCycle (fromProjectiveState y)) = projectiveCycle y := by
  have hr : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  have hr2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have Hclock := axisCycle_inverse_clock hD
  have HH := projectiveCycleDenom_eq y
  ext i
  fin_cases i <;> change Real.sqrt 3 * axisCycle (fromProjectiveState y) _ /
    (1 + axisCycle (fromProjectiveState y) 0) = _ <;> rw [Hclock]
  · change Real.sqrt 3 * ((-Real.sqrt 3 * (6 / projectiveStateDenom y - 1) -
        6 / projectiveStateDenom y * y 0 / Real.sqrt 3) / 2) /
        (6 / projectiveStateDenom y * projectiveCycleDenom y / 4) =
      1 - 4 * (y 0 + 1) / projectiveCycleDenom y
    field_simp
    ring_nf
    rw [hr2]
    nlinarith only [HH]
  all_goals
    dsimp [axisCycle, fromProjectiveState, projectiveCycle]
    field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_projective_clock {x : NormalizedState} (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) :
    1 + axisCycle x 0 = (1 + x 0) * projectiveCycleDenom (toProjectiveState x) / 4 := by
  have hD : projectiveStateDenom (toProjectiveState x) ≠ 0 := by
    have HD : projectiveStateDenom (toProjectiveState x) = 6 / (1 + x 0) := projectiveDenom_of_constraint hA hc
    rw [HD]
    exact div_ne_zero (by norm_num) hA
  have H := axisCycle_inverse_clock hD
  rw [fromProjectiveState_toProjectiveState hA hc] at H
  have Hscale : 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 := projective_inverse_scale hA hc
  rwa [Hscale] at H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.toProjectiveState_axisCycle {x : NormalizedState} (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1)
    (hH : projectiveCycleDenom (toProjectiveState x) ≠ 0) :
    toProjectiveState (axisCycle x) = projectiveCycle (toProjectiveState x) := by
  have hD : projectiveStateDenom (toProjectiveState x) ≠ 0 := by
    have HD : projectiveStateDenom (toProjectiveState x) = 6 / (1 + x 0) := projectiveDenom_of_constraint hA hc
    rw [HD]
    exact div_ne_zero (by norm_num) hA
  have H := toProjectiveState_axisCycle_inverse hD hH
  rwa [fromProjectiveState_toProjectiveState hA hc] at H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.axisCycle_projective_clock_pos {x : NormalizedState} (hA : 0 < 1 + x 0) (hc : stateConstraint x = 1)
    (hH : 0 < projectiveCycleDenom (toProjectiveState x)) :
    0 < 1 + axisCycle x 0 ∧ (1 + axisCycle x 0) / (1 + x 0) = projectiveCycleDenom (toProjectiveState x) / 4 := by
  rw [axisCycle_projective_clock hA.ne' hc]
  exact ⟨div_pos (mul_pos hA hH) (by norm_num), by field_simp⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailState_active {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    coreTailState η Y 2 = η := hvalid.1.1.2.2

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailValid_denom_pos {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    0 < projectiveStateDenom (coreTailEntry Y) := by
  have hzero := (hvalid.2.1 0 ⟨le_rfl, hvalid.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at hzero
  by_contra! hn
  have H := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, H]

end
end


/-- The cyclic chart stays regular along the entire actual tail and cannot encounter its new active section early. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η ≤ 1 / 100) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let x := fromProjectiveState (coreTailEntry Y)
      let γ := fun t => normalizedMaxCurve x 0 t
      let γc := fun t => normalizedMaxCurve (axisCycle x) 0 t
      let β := fun t => toProjectiveState (γ t)
      let βc := fun t => toProjectiveState (γc t)
      coreTailValid h Y ∧ C * b ≤ α ^ (2 * J) / 10000 ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y),
          β t 0 < 1 ∧ |coreRadius (β t 0) (β t 2) - (2 + 2 * α)| ≤ C * b ∧
          |β t 1| + |β t 3| ≤ C * b ∧
          39 / 10 * α ^ 2 + 2 / 5 * (β t 2) ^ 2 < projectiveCycleDenom (β t) ∧
          0 < 1 + γc t 0 ∧ βc t = projectiveCycle (β t) ∧
          (1 + γc t 0) / (1 + γ t 0) = projectiveCycleDenom (β t) / 4 ∧
          |βc t 2| ≤ 2 * (C * b) / α ^ 2 ∧ |βc t 2| ≤ 1 / 5000) ∧
        399 / 100 * α ^ 2 < projectiveCycleDenom (coreTailState h Y) ∧
        projectiveCycleDenom (coreTailState h Y) < 401 / 100 * α ^ 2 := by
  have hη1 : η < 1 := by linarith only [hη.2]
  obtain ⟨A, hA, εt, hεt, HE⟩ := exists_terminal_coreTail_valid ⟨hη.1, hη1⟩ hJ
  let C := 40 * A
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hA]
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let ε := min εt (1 / (10000 * C))
  have hε : 0 < ε := lt_min hεt (by positivity)
  have hCε : C * ε ≤ 1 / 10000 := by
    have H := (le_div_iff₀ (by positivity : 0 < 10000 * C)).mp (min_le_right εt (1 / (10000 * C)))
    nlinarith only [H]
  refine ⟨C, hC, ε, hε, ?_⟩
  intro α b u w hα hb hsmall hw Y h x γ γc β βc
  have hα0 : 0 < α := hα.1
  have hpJ : α ^ (2 * J) ≤ α ^ J := pow_le_pow_of_le_one hα.1.le hα.2 (by omega)
  have hp2 : α ^ (2 * J) ≤ α ^ 2 := pow_le_pow_of_le_one hα.1.le hα.2 (by omega)
  have hsmallt : b ≤ εt * α ^ J := hsmall.trans ((mul_le_mul_of_nonneg_left hpJ hε.le).trans
    (mul_le_mul_of_nonneg_right (min_le_left εt _) (pow_nonneg hα.1.le J)))
  have hCBpow : C * b ≤ α ^ (2 * J) / 10000 := by
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hC0.le,
      mul_le_mul_of_nonneg_right hCε (pow_nonneg hα.1.le (2 * J))]
  have hCBsq : C * b ≤ α ^ 2 / 10000 := hCBpow.trans (div_le_div_of_nonneg_right hp2 (by norm_num))
  have hCB : C * b ≤ α / 10000 := hCBsq.trans (by nlinarith only [hα.1, hα.2])
  obtain ⟨hvalid, hT, _, HF⟩ := HE α b u w hα hb hsmallt hw
  change coreTailValid h Y at hvalid
  have hc : stateConstraint x = 1 := fromProjectiveState_constraint (coreTailValid_denom_pos hvalid).ne'
  have hraw (t : ℝ) (ht : t ∈ Icc 0 (coreTailTime h Y)) :
      0 < 1 + γ t 0 ∧ (β t 0 < 1) ∧ (0 ≤ β t 2 ∧ β t 2 ≤ 1) ∧
      |coreRadius (β t 0) (β t 2) - (2 + 2 * α)| ≤ C * b ∧ |β t 1| + |β t 3| ≤ C * b := by
    have H := HF t ht
    have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
    refine ⟨lt_of_lt_of_le (by norm_num) H.1, lt_of_le_of_lt H.2.1.1 (by norm_num),
      ⟨hh.le.trans H.2.1.2.2.2.1.1, H.2.1.2.2.2.1.2⟩, H.2.2.2.1, ?_⟩
    exact H.2.2.1.trans (by dsimp only [C]; nlinarith only [mul_nonneg (by linarith only [hA] : 0 ≤ A) hb.le])
  have hgap (t : ℝ) (ht : t ∈ Icc 0 (coreTailTime h Y)) :
      1 - exitTailGap (coreRadius (β t 0) (β t 2)) (β t 2) = β t 0 := by
    rw [exitTailGap_of_coreRadius (hraw t ht).2.1]
    ring
  refine ⟨hvalid, hCBpow, ?_, ?_⟩
  · intro t ht
    have H := hraw t ht
    have HH := exitCycleDenom_lower hα hCB H.2.2.2.1 H.2.2.2.2 H.2.2.1
    rw [hgap t ht] at HH
    change 39 / 10 * α ^ 2 + 2 / 5 * (β t 2) ^ 2 < projectiveCycleDenom (β t) at HH
    have HH' : 39 / 10 * α ^ 2 < projectiveCycleDenom (β t) := by nlinarith only [HH, sq_nonneg (β t 2)]
    have HH0 : 0 < projectiveCycleDenom (β t) := lt_trans (by positivity) HH'
    have hct : stateConstraint (γ t) = 1 := (normalizedMaxCurve_forward_of_constraint hc ht.1).2.1
    have hcycle : γc t = axisCycle (γ t) := NormalizedSymmetry.cycle.maxCurve
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1)
    have Hclock := axisCycle_projective_clock_pos H.1 hct HH0
    have Hmap := toProjectiveState_axisCycle H.1.ne' hct HH0.ne'
    have Hcmap : βc t = projectiveCycle (β t) := by change toProjectiveState (γc t) = _; rwa [hcycle]
    have Hweak : |β t 3| ≤ C * b := by linarith only [H.2.2.2.2, abs_nonneg (β t 1)]
    refine ⟨H.2.1, H.2.2.2.1, H.2.2.2.2, HH, by rw [hcycle]; exact Hclock.1,
      Hcmap, by rw [hcycle]; exact Hclock.2, ?_, ?_⟩
    · rw [Hcmap]
      exact exitCycle_newWall_bound hα.1 (mul_pos hC0 hb).le HH' Hweak
    · rw [Hcmap]
      exact exitCycle_newWall_small hα.1 (mul_pos hC0 hb).le hCBsq HH' Hweak
  · have ht : coreTailTime h Y ∈ Icc 0 (coreTailTime h Y) := ⟨hT.le, le_rfl⟩
    have H := hraw _ ht
    have hv : β (coreTailTime h Y) 2 = h := coreTailState_active hvalid
    have hp : α ^ J ≤ α := (pow_le_pow_of_le_one hα.1.le hα.2 hJ).trans_eq (pow_one α)
    have hvsmall : β (coreTailTime h Y) 2 ≤ α / 100 := by
      rw [hv]
      change η * α ^ J ≤ α / 100
      nlinarith only [mul_le_mul_of_nonneg_left hp hη.1.le, mul_le_mul_of_nonneg_right hη.2 hα.1.le]
    have HB := exitCycleDenom_terminal_bounds hα hCB H.2.2.2.1 H.2.2.2.2 ⟨H.2.2.1.1, hvsmall⟩
    rw [hgap _ ht] at HB
    exact HB
