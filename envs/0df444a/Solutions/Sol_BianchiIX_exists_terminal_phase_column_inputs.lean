-- Prove2me | solution 1 for BianchiIX.exists_terminal_phase_column_inputs
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:26:07.374429+00:00
-- url     : https://prove2.me/submissions/2209ea24-60f2-44d6-9fe9-f26856404448

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_EntrancePhaseResponseData
import Theorems.Thm_BianchiIX_exists_entrance_terminal_phase_bounds
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_endpoint_uniform
import Theorems.Thm_BianchiIX_exists_terminal_cycle_entrance_inputs_uniform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitCycle_scaled_wall_power {α B δ : ℝ} {p : ℕ}
    (hα : 0 < α) (hp : 2 ≤ p) (hB : B ≤ δ * α ^ p) :
    2 * B / α ^ 2 ≤ 2 * δ * α ^ (p - 2) := by
  apply (div_le_iff₀ (sq_pos_of_pos hα)).mpr
  have hpα : α ^ p = α ^ (p - 2) * α ^ 2 := by rw [← pow_add, Nat.sub_add_cancel hp]
  rw [hpα] at hB
  nlinarith only [hB]

end
end


/-- One entrance threshold supplies the actual phase columns uniformly in the terminal height. -/
theorem solution :
    ∃ A ≥ (1 : ℝ), ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η₀ : ℝ,
      (0 < η₀ ∧ η₀ ≤ δ) → ∀ J : ℕ, 2 ≤ J →
      ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let y := terminalCyclicInput h Y
      coreTailValid h Y ∧ 0 < projectiveCycleDenom (coreTailState h Y) ∧
        (0 < y 1 ∧ y 1 ≤ 1) ∧ (0 < y 2 ∧ y 2 < 1) ∧ (0 < y 3 ∧ y 3 ≤ 1) ∧ y 3 ≤ y 1 ∧
        ∃ Ψ : ProjectiveState → ProjectiveState, EntranceRadialInverseAt y Ψ ∧
        let z := terminalEntranceInput h Y
        let F := fun z => coreRadius (entranceReturnState (Ψ z) 0) (entranceReturnState (Ψ z) 2)
        ContDiffAt ℝ 2 F z ∧ |F z - z 0| ≤ A * α * y 1 * y 2 ∧
          |fderiv ℝ F z (Pi.single 0 1) - 1| ≤ A * y 1 * y 2 ∧
          |fderiv ℝ F z (Pi.single 1 1)| ≤ A * α * y 2 ∧
          |fderiv ℝ F z (Pi.single 2 1)| ≤ A * y 1 ∧
          |fderiv ℝ F z (Pi.single 3 1)| ≤ A * α * y 1 * y 2 := by
  obtain ⟨A, hA, δin, hδin, hδinhi, HA⟩ := exists_entrance_terminal_phase_bounds
  let δ := min (δin / 4) (1 / 1000)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  refine ⟨A, hA, δ, hδ, min_le_right _ _, ?_⟩
  intro η₀ hη₀ J hJ
  have hη₀pos : 0 < η₀ := hη₀.1
  have hη₀hi : η₀ ≤ 1 / 100 := (hη₀.2.trans (min_le_right _ _)).trans (by norm_num)
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs_uniform hδin ⟨hη₀.1, hη₀hi⟩
    (q := 0) (by omega : 0 + 2 ≤ J)
  obtain ⟨B, hB, εg, hεg, HG⟩ := exists_terminal_axisCycle_endpoint_uniform ⟨hη₀.1, hη₀hi⟩ hJ
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  let ε := min εi (min εg (η₀ / (4 * B)))
  refine ⟨ε, lt_min hεi (lt_min hεg (by positivity)), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h y
  have hα0 : 0 < α := hα.1
  have hη100 : η ≤ 1 / 100 := (hηhi.trans (min_le_right _ _)).trans (by norm_num)
  have hηin : η ≤ δin / (4 * (11 / 5) ^ (0 : ℕ)) := by
    simpa only [pow_zero, mul_one] using hηhi.trans (min_le_left _ _)
  have hsi := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le (2 * J)))
  have hsg := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, _, HK, HM, HU, HVwall, HW, _, HH⟩ := HI η α b u w hηlo hη100 hηin hα hb hsi hsum hu hw
  obtain ⟨_, _, _, _, Hrad, HUscale, HWscale, _, _, _⟩ := HG η α b u w hηlo hη100 hα hb hsg hsum
  change 2 < y 0 at HM
  change 0 < y 2 ∧ y 2 < 1 / 2 at HVwall
  change 19 / (10 * α) < coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) < 11 / (5 * α) at Hrad
  have hka : 1 / α ≤ coreRadius (y 0) (y 2) := le_trans (by
    apply (div_le_div_iff₀ hα.1 (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.1]) Hrad.1.le
  have hbudget : B * b ≤ η₀ / 4 * α ^ (2 * J) := by
    have Hε := (le_div_iff₀ (mul_pos (by norm_num) hB0)).mp
      ((min_le_right εi (min εg (η₀ / (4 * B)))).trans (min_le_right _ _))
    nlinarith only [mul_le_mul_of_nonneg_left hsmall hB0.le,
      mul_le_mul_of_nonneg_right Hε (pow_nonneg hα.1.le (2 * J))]
  have Hweak : y 3 ≤ η₀ / 2 * α ^ (2 * J - 2) := by
    have H := (le_abs_self _).trans (HWscale.2.trans
      (exitCycle_scaled_wall_power hα.1 (by omega : 2 ≤ 2 * J) hbudget))
    change y 3 ≤ 2 * (η₀ / 4) * α ^ (2 * J - 2) at H
    convert H using 1
    ring
  have hwu : y 3 ≤ y 1 := Hweak.trans ((mul_le_mul
    (by linarith only [hηlo] : η₀ / 2 ≤ η / 2)
    (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : J - 2 ≤ 2 * J - 2))
    (pow_nonneg hα.1.le (2 * J - 2)) (by linarith only [hη₀.1, hηlo] : 0 ≤ η / 2)).trans HUscale.1)
  have hV : 0 < y 2 ∧ y 2 < 1 := ⟨HVwall.1, by linarith only [HVwall.2]⟩
  have hin1 : δin ≤ 1 := hδinhi.trans (by norm_num)
  refine ⟨HV, HH, ⟨HU.1, HU.2.1.trans hin1⟩, hV, ⟨HW.1, HW.2.1.trans hin1⟩, hwu, ?_⟩
  exact HA α y hα hka HK.le (by linarith only [HM]) ⟨HU.1, HU.2.1⟩ hV ⟨HW.1, HW.2.1⟩ hwu
