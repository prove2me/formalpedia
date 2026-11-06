-- Prove2me | solution 1 for BianchiIX.exists_terminal_axisCycle_endpoint_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:33:32.500708+00:00
-- url     : https://prove2.me/submissions/3b3a0113-2c6a-4db8-a055-fdabbaf27f62

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreTailMultipliers
import Theorems.Thm_BianchiIX_coreTailMultiplier_formula
import Theorems.Thm_BianchiIX_coreTailValid_of_height_le
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_regular
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

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

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

private theorem BianchiIX.exitTailGap_terminal_offset {α B R v : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    199 / 100 * α < exitTailGap R v - 2 ∧ exitTailGap R v - 2 < 201 / 100 * α := by
  have hα0 : 0 < α := hα.1
  have hRc := abs_le.mp hR
  have hRlo : 2 + 19999 / 10000 * α ≤ R := by linarith only [hRc.1, hB]
  have hR0 : 0 ≤ R := by linarith only [hRlo, hα.1]
  have hRsq := (sq_le_sq₀ (by positivity) hR0).mpr hRlo
  have hvsq := (sq_le_sq₀ hv.1 (by positivity)).mpr hv.2
  have hvR : v ^ 2 ≤ R ^ 2 := by nlinarith only [hRsq, hvsq, hα.1, sq_nonneg α]
  have ht := exitTailGap_sq hvR
  have ht0 : 0 ≤ exitTailGap R v := Real.sqrt_nonneg _
  have hs : (2 + 199 / 100 * α) ^ 2 < (exitTailGap R v) ^ 2 := by
    nlinarith only [hRsq, hvsq, ht, hα.1, sq_nonneg α]
  have hlo := (sq_lt_sq₀ (by positivity) ht0).mp hs
  have hhi : exitTailGap R v ≤ R := (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])
  constructor <;> linarith only [hlo, hhi, hRc.2, hB, hα.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_terminal_phase_bounds {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    19 / (10 * α) < 4 * (exitTailGap R v - 2) / axisCycleDenom (1 - exitTailGap R v) u v w ∧
      4 * (exitTailGap R v - 2) / axisCycleDenom (1 - exitTailGap R v) u v w < 21 / (10 * α) := by
  have hα0 : 0 < α := hα.1
  have HH := exitCycleDenom_terminal_bounds hα hB hR hw hv
  have HG := exitTailGap_terminal_offset hα hB hR hv
  have hH0 : 0 < axisCycleDenom (1 - exitTailGap R v) u v w := lt_trans (by positivity) HH.1
  constructor
  · apply (div_lt_div_iff₀ (by positivity) hH0).mpr
    nlinarith only [HH.2, mul_lt_mul_of_pos_right HG.1 hα.1, sq_pos_of_pos hα.1]
  · apply (div_lt_div_iff₀ hH0 (by positivity)).mpr
    nlinarith only [HH.1, mul_lt_mul_of_pos_right HG.2 hα.1, sq_pos_of_pos hα.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_terminal_radius_bounds {α B R u v w : ℝ} (hα : 0 < α ∧ α ≤ 1)
    (hB : B ≤ α ^ 2 / 10000) (hR : |R - (2 + 2 * α)| ≤ B)
    (hw : |u| + |w| ≤ B) (hv : 0 ≤ v ∧ v ≤ α / 100) :
    let H := axisCycleDenom (1 - exitTailGap R v) u v w
    let m := 1 - 4 * (2 - exitTailGap R v) / H
    19 / (10 * α) < coreRadius m (4 * w / H) ∧ coreRadius m (4 * w / H) < 11 / (5 * α) := by
  intro H m
  have hα0 : 0 < α := hα.1
  have hB0 : 0 ≤ B := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans hw
  have hBlin : B ≤ α / 10000 := hB.trans (by nlinarith only [hα.1, hα.2])
  have HH := exitCycleDenom_terminal_bounds hα hBlin hR hw hv
  have Hphase := exitCycle_terminal_phase_bounds hα hBlin hR hw hv
  have hm : m - 1 = 4 * (exitTailGap R v - 2) / H := by dsimp only [m]; ring
  change 19 / (10 * α) < 4 * (exitTailGap R v - 2) / H ∧
    4 * (exitTailGap R v - 2) / H < 21 / (10 * α) at Hphase
  rw [← hm] at Hphase
  have hm0 : 0 < m - 1 := lt_trans (by positivity) Hphase.1
  have hH : 39 / 10 * α ^ 2 < H := by nlinarith only [HH.1, sq_pos_of_pos hα.1]
  have hwB : |w| ≤ B := by linarith only [hw, abs_nonneg u]
  have HW := exitCycle_newWall_small hα.1 hB0 hB hH hwB
  have hlo : m - 1 ≤ coreRadius m (4 * w / H) := phaseNorm_ge hm0.le
  have hhi : coreRadius m (4 * w / H) ≤ (m - 1) + 1 / 5000 := by
    have HE := phaseNorm_le_abs_add (m - 1) (4 * w / H)
    rw [abs_of_pos hm0] at HE
    exact HE.trans (add_le_add_right HW (m - 1))
  refine ⟨Hphase.1.trans_le hlo, ?_⟩
  apply (lt_div_iff₀ (by positivity : 0 < 5 * α)).mpr
  have HM := (lt_div_iff₀ (by positivity : 0 < 10 * α)).mp Hphase.2
  nlinarith only [HM, mul_le_mul_of_nonneg_right hhi hα.1.le, hα.2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_positive_wall_scale {α H v : ℝ} (hα : 0 < α) (hv : 0 ≤ v)
    (hH : 399 / 100 * α ^ 2 < H ∧ H < 401 / 100 * α ^ 2) :
    v / (2 * α ^ 2) ≤ 4 * v / H ∧ 4 * v / H ≤ 2 * v / α ^ 2 := by
  have hH0 : 0 < H := lt_trans (by positivity) hH.1
  constructor
  · apply (div_le_div_iff₀ (by positivity) hH0).mpr
    have HH : H ≤ 8 * α ^ 2 := by nlinarith only [hH.2, sq_nonneg α]
    nlinarith only [mul_le_mul_of_nonneg_left HH hv]
  · have HB : |4 * v / H| ≤ 2 * v / α ^ 2 := exitCycle_newWall_bound hα hv
      (by nlinarith only [hH.1, sq_pos_of_pos hα]) (by rw [abs_of_nonneg hv])
    exact (le_abs_self _).trans HB

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.normalizedProjectiveWallMultiplier_pos (x : NormalizedState) (T : ℝ) (i : Fin 3) :
    0 < normalizedProjectiveWallMultiplier x T i := Real.exp_pos _

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

private theorem BianchiIX.coreTailMultiplier_pos (η : ℝ) (Y : CoreAngleState) (i : Fin 2) :
    0 < coreTailMultiplier η Y i := normalizedProjectiveWallMultiplier_pos _ _ _

end
end


/-- Constants chosen at the lowest height control all higher terminal heights at once. -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 100)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 100 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let y := coreTailState h Y
      let z := projectiveCycle y
      coreTailValid h Y ∧
        toProjectiveState (normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 (coreTailTime h Y)) = z ∧
        (399 / 100 * α ^ 2 < projectiveCycleDenom y ∧ projectiveCycleDenom y < 401 / 100 * α ^ 2) ∧
        (19 / (10 * α) < z 0 - 1 ∧ z 0 - 1 < 21 / (10 * α)) ∧
        (19 / (10 * α) < coreRadius (z 0) (z 2) ∧ coreRadius (z 0) (z 2) < 11 / (5 * α)) ∧
        (η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2)) ∧
        (|z 2| ≤ 2 * (C * b) / α ^ 2 ∧ |z 3| ≤ 2 * (C * b) / α ^ 2) ∧
        ((0 < u ∧ 0 < w) → 0 < z 2 ∧ 0 < z 3) ∧
        (∀ t ∈ Icc 0 (coreTailTime h Y),
          let γ := normalizedMaxCurve (axisCycle (fromProjectiveState (coreTailEntry Y))) 0 t
          0 < 1 + γ 0 ∧ |toProjectiveState γ 2| ≤ 1 / 5000) ∧
        C * b ≤ α ^ (2 * J) / 10000 := by
  obtain ⟨C, hC, ε, hε, HE⟩ := exists_terminal_axisCycle_regular hη₀ (by omega : 1 ≤ J)
  refine ⟨C, hC, ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hw Y h y z
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hα0 : 0 < α := hα.1
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  obtain ⟨HV₀, hCBpow, HF₀, _⟩ := HE α b u w hα hb hsmall hw
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.le
    dsimp only [h]
    nlinarith only [H, hηhi]
  obtain ⟨HV, htime⟩ := coreTailValid_of_height_le HV₀
    (mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)) hh1
  change coreTailValid h Y at HV
  have hsub : Icc 0 (coreTailTime h Y) ⊆ Icc 0 (coreTailTime (η₀ * α ^ J) Y) :=
    fun _ ht => ⟨ht.1, ht.2.trans htime⟩
  have ht : coreTailTime h Y ∈ Icc 0 (coreTailTime h Y) := ⟨HV.1.1.1.le, le_rfl⟩
  have H := HF₀ _ (hsub ht)
  have hm : y 0 < 1 := H.1
  have hR : |coreRadius (y 0) (y 2) - (2 + 2 * α)| ≤ C * b := H.2.1
  have hsum : |y 1| + |y 3| ≤ C * b := H.2.2.1
  have hv : y 2 = h := coreTailState_active HV
  have hh : 0 < h := mul_pos hη (pow_pos hα.1 J)
  have hp2 : α ^ (2 * J) ≤ α ^ 2 := pow_le_pow_of_le_one hα.1.le hα.2 (by omega)
  have hCBsq : C * b ≤ α ^ 2 / 10000 := hCBpow.trans (div_le_div_of_nonneg_right hp2 (by norm_num))
  have hCB : C * b ≤ α / 10000 := hCBsq.trans (by nlinarith only [hα.1, hα.2])
  have hvsmall : 0 ≤ y 2 ∧ y 2 ≤ α / 100 := by
    rw [hv]
    refine ⟨hh.le, ?_⟩
    have hp : α ^ J ≤ α := (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 1 ≤ J)).trans_eq (pow_one α)
    change η * α ^ J ≤ α / 100
    nlinarith only [mul_le_mul_of_nonneg_left hp hη.le, mul_le_mul_of_nonneg_right hηhi hα.1.le]
  have hsplit : 1 - exitTailGap (coreRadius (y 0) (y 2)) (y 2) = y 0 := by
    rw [exitTailGap_of_coreRadius hm]
    ring
  have hdelta : 2 - exitTailGap (coreRadius (y 0) (y 2)) (y 2) = y 0 + 1 := by linarith only [hsplit]
  have HH := exitCycleDenom_terminal_bounds hα hCB hR hsum hvsmall
  rw [hsplit] at HH
  change 399 / 100 * α ^ 2 < projectiveCycleDenom y ∧ projectiveCycleDenom y < 401 / 100 * α ^ 2 at HH
  have HP := exitCycle_terminal_phase_bounds hα hCB hR hsum hvsmall
  rw [hsplit] at HP
  have hphase : z 0 - 1 = 4 * (exitTailGap (coreRadius (y 0) (y 2)) (y 2) - 2) / projectiveCycleDenom y := by
    change 1 - 4 * (y 0 + 1) / projectiveCycleDenom y - 1 = _
    rw [← hdelta]
    ring
  have HK := exitCycle_terminal_radius_bounds hα hCBsq hR hsum hvsmall
  dsimp only at HK
  rw [hsplit, hdelta] at HK
  have Hwall := exitCycle_positive_wall_scale hα.1 hvsmall.1 HH
  have hpow : h = η * α ^ (J - 2) * α ^ 2 := by
    change η * α ^ J = _
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hJ]
  have Hstrong : η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) := by
    change _ ≤ 4 * y 2 / projectiveCycleDenom y ∧ 4 * y 2 / projectiveCycleDenom y ≤ _
    constructor
    · convert Hwall.1 using 1
      rw [hv, hpow]
      field_simp
    · convert Hwall.2 using 1
      rw [hv, hpow]
      field_simp
  have HH' : 39 / 10 * α ^ 2 < projectiveCycleDenom y := by nlinarith only [HH.1, sq_pos_of_pos hα.1]
  have HH0 : 0 < projectiveCycleDenom y := lt_trans (by positivity) HH'
  refine ⟨HV, H.2.2.2.2.2.1, HH, ?_, HK, Hstrong, ?_, ?_, ?_, hCBpow⟩
  · rw [hphase]
    exact HP
  · exact ⟨exitCycle_newWall_bound hα.1 (mul_pos hC0 hb).le HH' (by linarith only [hsum, abs_nonneg (y 1)]),
      exitCycle_newWall_bound hα.1 (mul_pos hC0 hb).le HH' (by linarith only [hsum, abs_nonneg (y 3)])⟩
  · intro hpos
    have HU : y 1 = u * coreTailMultiplier h Y 0 := coreTailMultiplier_formula HV 0
    have HW : y 3 = w * coreTailMultiplier h Y 1 := coreTailMultiplier_formula HV 1
    have hu : 0 < y 1 := by rw [HU]; exact mul_pos hpos.1 (coreTailMultiplier_pos _ _ _)
    have hw : 0 < y 3 := by rw [HW]; exact mul_pos hpos.2 (coreTailMultiplier_pos _ _ _)
    exact ⟨div_pos (mul_pos (by norm_num) hw) HH0, div_pos (mul_pos (by norm_num) hu) HH0⟩
  · intro t ht
    have Ht := HF₀ t (hsub ht)
    exact ⟨Ht.2.2.2.2.1, Ht.2.2.2.2.2.2.2.2⟩
