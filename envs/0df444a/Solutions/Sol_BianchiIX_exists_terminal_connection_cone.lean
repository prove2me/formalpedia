-- Prove2me | solution 1 for BianchiIX.exists_terminal_connection_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:45:48.921197+00:00
-- url     : https://prove2.me/submissions/89529f8f-adbe-40ec-adeb-2244cdcc9b73

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_terminal_connection_cone_scales
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

noncomputable section
open BianchiIX
open Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.terminal_cone_power_budget {α b U W : ℝ} {J : ℕ} (hJ : 5 ≤ J)
    (hα : 0 < α ∧ α ≤ 1) (hb : 0 < b ∧ b ≤ 1) (hU : 0 ≤ U) (hW : 0 < W)
    (hsum : U + W ≤ b) :
    α ^ (((J : ℝ) - 5) / 2) * W ^ (3 / 4 : ℝ) +
      α ^ ((J : ℝ) / 2 - 19 / 12) * W ^ (7 / 24 : ℝ) ≤ 2 * b ^ (7 / 24 : ℝ) ∧
      Real.sqrt U + Real.sqrt W ≤ 2 * b ^ (7 / 24 : ℝ) := by
  have hJr : (5 : ℝ) ≤ J := by exact_mod_cast hJ
  have hWb : W ≤ b := by linarith only [hsum, hU]
  have hUb : U ≤ b := by linarith only [hsum, hW]
  have h3 : W ^ (3 / 4 : ℝ) ≤ b ^ (7 / 24 : ℝ) :=
    (Real.rpow_le_rpow hW.le hWb (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_ge hb.1 hb.2 (by norm_num))
  have h7 : W ^ (7 / 24 : ℝ) ≤ b ^ (7 / 24 : ℝ) := Real.rpow_le_rpow hW.le hWb (by norm_num)
  have hα1 := Real.rpow_le_one hα.1.le hα.2 (by linarith only [hJr] : 0 ≤ ((J : ℝ) - 5) / 2)
  have hα2 := Real.rpow_le_one hα.1.le hα.2 (by linarith only [hJr] : 0 ≤ (J : ℝ) / 2 - 19 / 12)
  have hs : Real.sqrt b ≤ b ^ (7 / 24 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hb.1 hb.2 (by norm_num)
  constructor
  · have H1 := (mul_le_of_le_one_left (Real.rpow_nonneg hW.le _) hα1).trans h3
    have H2 := (mul_le_of_le_one_left (Real.rpow_nonneg hW.le _) hα2).trans h7
    linarith only [H1, H2]
  · linarith only [(Real.sqrt_le_sqrt hUb).trans hs, (Real.sqrt_le_sqrt hWb).trans hs]

end
end


/-- Formula (D.38): the actual terminal connection reverses phase and strictly contracts
every square-root cone direction, uniformly over the positive wall ratio. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 5 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b U W : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |U| + |W| ≤ b → 0 < U → 0 < W →
      let Y : ExitTailState := ![2 + 2 * α, U, W]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalConnectionState h) Y ∧
        ContDiffAt ℝ 2 (terminalConnectionPhase h) Y ∧
        0 < terminalConnectionState h Y 1 ∧ 0 < terminalConnectionState h Y 3 ∧
        C * b ^ (7 / 24 : ℝ) < 1 / 2 ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt U → |d 2| ≤ Real.sqrt W →
          let p := fderiv ℝ (terminalConnectionPhase h) Y d
          p < 0 ∧ 3 / (4 * α ^ 2) ≤ |p| ∧
          max (|fderiv ℝ (terminalConnectionState h) Y d 1| / (Real.sqrt (terminalConnectionState h Y 1) * |p|))
            (|fderiv ℝ (terminalConnectionState h) Y d 3| / (Real.sqrt (terminalConnectionState h Y 3) * |p|)) ≤
              C * b ^ (7 / 24 : ℝ) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_connection_cone_scales
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  obtain ⟨A, hA, ε₀, hε₀, HA⟩ := HE η₀ hη₀ J (by omega)
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  let C := 2 * A
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hA]
  obtain ⟨ε, hε, hεmax, Hbudget⟩ := exists_common_rpow_budget (ι := Fin 1) Finset.univ
    (C := fun _ => C) (p := fun _ => 7 / 24) (ε := fun _ => 1 / 2)
    (by intros; dsimp only [C]; positivity) (by intros; norm_num) (by intros; norm_num)
    (lt_min hε₀ (by norm_num : (0 : ℝ) < 1))
  refine ⟨C, hC, ε, hε, ?_⟩
  intro η α b U W hηlo hηhi hα hb hsmall hsum hU hW Y h
  have hbε : b ≤ ε := hsmall.trans (mul_le_of_le_one_right hε.le (pow_le_one₀ hα.1.le hα.2))
  have hb1 : b ≤ 1 := hbε.trans (hεmax.le.trans (min_le_right _ _))
  have hs := hsmall.trans (mul_le_mul_of_nonneg_right (hεmax.le.trans (min_le_left _ _)) (pow_nonneg hα.1.le _))
  obtain ⟨HV, Hstate, Hphase, HU, HW, Hcone⟩ := HA η α b U W hηlo hηhi hα hb hs hsum hU hW
  have Hpowers := terminal_cone_power_budget hJ hα ⟨hb, hb1⟩ hU.le hW
    (by simpa only [abs_of_pos hU, abs_of_pos hW] using hsum)
  refine ⟨HV, Hstate, Hphase, HU, HW, Hbudget b ⟨hb, hbε⟩ 0 (Finset.mem_univ _), ?_⟩
  intro d hd0 hd1 hd2 p
  obtain ⟨Hneg, Hp, Hstrong, Hweak⟩ := Hcone d hd0 hd1 hd2
  refine ⟨Hneg, Hp, max_le ?_ ?_⟩
  · exact (Hstrong.trans (mul_le_mul_of_nonneg_left Hpowers.1 hA0)).trans_eq (by dsimp only [C]; ring)
  · exact (Hweak.trans (mul_le_mul_of_nonneg_left Hpowers.2 hA0)).trans_eq (by dsimp only [C]; ring)
