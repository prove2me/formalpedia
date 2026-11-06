-- Prove2me | solution 1 for BianchiIX.exists_terminal_entrance_radius_lower
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:22:45.657161+00:00
-- url     : https://prove2.me/submissions/c0f6b76d-2844-499e-8857-85d9040235e3

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_endpoint_uniform
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalized_stable_limit
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

noncomputable section
open BianchiIX

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
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryEntry_denom_pos (m u w : ℝ) :
    0 < projectiveStateDenom (stableBoundaryEntry m u w) := by
  change 0 < projectiveDenom m u 0 w
  have H : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [H]
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_initial (m u w : ℝ) :
    stableBoundaryOrbit m u w 0 = stableBoundaryEntry m u w := by
  unfold stableBoundaryOrbit
  rw [normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (stableBoundaryEntry_denom_pos m u w))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_exists {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (fun t => stableBoundaryOrbit m u w t 0) atTop (𝓝 (stableBoundaryProjection m u w)) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 1) atTop (𝓝 0) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 3) atTop (𝓝 0) ∧
    (∀ t ≥ 0, |stableBoundaryProjection m u w - stableBoundaryOrbit m u w t 0| ≤
      8 * (|stableBoundaryOrbit m u w t 1| + |stableBoundaryOrbit m u w t 3|) ^ 2 / (c + 1)) ∧
    |stableBoundaryProjection m u w - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_limit hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  obtain ⟨P, hP, hU, hW, htail⟩ := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  have heq : stableBoundaryProjection m u w = P := hP.limUnder_eq
  rw [heq]
  refine ⟨hP, hU, hW, htail, ?_⟩
  have H0 := htail 0 le_rfl
  change |P - stableBoundaryOrbit m u w 0 0| ≤
    8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) at H0
  simpa [hi, stableBoundaryEntry] using H0

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.entranceStablePhase_signed_lower {y : ProjectiveState}
    (hm : 2 ≤ y 0) (hu : |y 1| ≤ 1 / 400) (hw : |y 3| ≤ 1 / 400) :
    |entranceStablePhase y - y 0| ≤ 1 / 100 ∧ 1 < entranceStablePhase y := by
  have hu' : |y 1| ≤ 1 / 200 := by linarith only [hu]
  have hw' : |y 3| ≤ 1 / 200 := by linarith only [hw]
  have H := (stableBoundaryProjection_exists hm (by simp : |y 0 - y 0| ≤ (1 : ℝ) / 40) hu' hw').2.2.2.2
  change |entranceStablePhase y - y 0| ≤ _ at H
  have hb : |y 1| + |y 3| ≤ 1 / 200 := by linarith only [hu, hw]
  have hb2 := pow_le_pow_left₀ (add_nonneg (abs_nonneg (y 1)) (abs_nonneg (y 3))) hb 2
  have HD : |entranceStablePhase y - y 0| ≤ 1 / 100 := H.trans
    ((div_le_iff₀ (by linarith only [hm] : 0 < y 0 + 1)).mpr (by nlinarith only [hb2, hm]))
  exact ⟨HD, by linarith only [(abs_le.mp HD).1, hm]⟩

end
end


theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 1000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 1000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ 3 / (2 * α) ≤ terminalEntranceInput h Y 0 := by
  obtain ⟨K, hK, ε, hε, HE⟩ := exists_terminal_axisCycle_endpoint_uniform
    ⟨hη₀.1, hη₀.2.trans (by norm_num)⟩ hJ
  refine ⟨ε, hε, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 := hα.1
  have hη0 : 0 < η := hη₀.1.trans_le hηlo
  obtain ⟨HV, _, _, HM, _, HU, HW, _, _, HB⟩ :=
    HE η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsmall hsum
  let z := terminalCyclicInput h Y
  change 19 / (10 * α) < z 0 - 1 ∧ z 0 - 1 < 21 / (10 * α) at HM
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at HU
  change |z 2| ≤ 2 * (K * b) / α ^ 2 ∧ |z 3| ≤ 2 * (K * b) / α ^ 2 at HW
  have Hlow : 19 / 10 ≤ 19 / (10 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.2]
  have hm : 2 ≤ z 0 := by linarith only [HM.1, Hlow]
  have hu : |z 1| ≤ 1 / 400 := by
    have hU0 : 0 ≤ z 1 := (by positivity : 0 ≤ η / 2 * α ^ (J - 2)).trans HU.1
    rw [abs_of_nonneg hU0]
    have Hpow := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J - 2)) (by positivity : 0 ≤ 2 * η)
    nlinarith only [HU.2, Hpow, hηhi]
  have hw : |z 3| ≤ 1 / 400 := by
    have HB' : K * b ≤ α ^ 2 / 10000 := HB.trans (div_le_div_of_nonneg_right
      (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)) (by norm_num))
    apply HW.2.trans ((div_le_iff₀ (sq_pos_of_pos hα.1)).mpr ?_)
    nlinarith only [HB', sq_nonneg α]
  have HP := entranceStablePhase_signed_lower hm hu hw
  have HR : entranceStablePhase z - 1 ≤ entranceStableRadius z := phaseNorm_ge (sub_pos.mpr HP.2).le
  refine ⟨HV, ?_⟩
  change 3 / (2 * α) ≤ entranceStableRadius z
  have Hphase := (div_lt_iff₀ (by positivity : 0 < 10 * α)).mp HM.1
  apply (div_le_iff₀ (by positivity : 0 < 2 * α)).mpr
  have HPmul := mul_le_mul_of_nonneg_right (abs_le.mp HP.1).1 hα.1.le
  have HRmul := mul_le_mul_of_nonneg_right HR hα.1.le
  nlinarith only [Hphase, HPmul, HRmul, hα.2]
