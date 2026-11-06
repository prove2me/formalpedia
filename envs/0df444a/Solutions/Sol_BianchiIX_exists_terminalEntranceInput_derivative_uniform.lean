-- Prove2me | solution 1 for BianchiIX.exists_terminalEntranceInput_derivative_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:26:16.731197+00:00
-- url     : https://prove2.me/submissions/1f9c5046-9301-4cca-baf5-4826f28852fd

import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_entranceRadialCoordinates_signed_bound
import Theorems.Thm_BianchiIX_exists_terminalCyclicInput_derivative_uniform
import Theorems.Thm_BianchiIX_exists_terminal_axisCycle_endpoint_uniform
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



/-- Formula (D.24) holds uniformly in height and in signed old wall amplitudes. -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 1000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 1000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalCyclicInput h) Y ∧
        ContDiffAt ℝ 2 (terminalEntranceInput h) Y ∧
        ‖fderiv ℝ (terminalCyclicInput h) Y‖ ≤ C / α ^ 2 ∧
        ‖fderiv ℝ (terminalEntranceInput h) Y‖ ≤ C / α ^ 2 ∧
        ‖fderiv ℝ (fun Z => Real.log (projectiveCycleDenom (coreTailState h Z))) Y‖ ≤ C / α := by
  have hη₀' : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, by linarith only [hη₀.2]⟩
  obtain ⟨A, hA, εc, hεc, HC⟩ := exists_terminalCyclicInput_derivative_uniform hη₀' (by omega : 1 ≤ J)
  obtain ⟨B, _, εz, hεz, HZ⟩ := exists_terminal_axisCycle_endpoint_uniform hη₀' hJ
  obtain ⟨K, hK, HK⟩ := exists_entranceRadialCoordinates_signed_bound
  have hK0 : 0 ≤ K := le_trans (by norm_num) hK
  have hscale : A ≤ K * A := by
    have H := mul_le_mul_of_nonneg_right hK (le_trans (by norm_num) hA)
    simpa only [one_mul] using H
  refine ⟨K * A, hA.trans hscale, min εc εz, lt_min hεc hεz, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hα0 : 0 < α := hα.1
  have hη100 : η ≤ 1 / 100 := by linarith only [hηhi]
  have hsmallc := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εc εz) (pow_nonneg hα.1.le (2 * J)))
  have hsmallz := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εc εz) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, Hreg, Hder, Hlog⟩ := HC η α b u w hηlo hη100 hα hb hsmallc hsum
  obtain ⟨_, _, _, HM, _, HU, HW, _, _, HB⟩ := HZ η α b u w hηlo hη100 hα hb hsmallz hsum
  let z := terminalCyclicInput h Y
  change 19 / (10 * α) < z 0 - 1 ∧ z 0 - 1 < 21 / (10 * α) at HM
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at HU
  change |z 2| ≤ 2 * (B * b) / α ^ 2 ∧ |z 3| ≤ 2 * (B * b) / α ^ 2 at HW
  have hlow : (19 / 10 : ℝ) ≤ 19 / (10 * α) := by
    apply (le_div_iff₀ (by positivity : 0 < 10 * α)).mpr
    linarith only [hα.2]
  have hm : 2 ≤ z 0 := by linarith only [HM.1, hlow]
  have hu0 : 0 < z 1 :=
    lt_of_lt_of_le (mul_pos (div_pos hη (by norm_num)) (pow_pos hα.1 (J - 2))) HU.1
  have hu : |z 1| ≤ 1 / 400 := by
    rw [abs_of_pos hu0]
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J - 2))
      (by positivity : 0 ≤ 2 * η)
    nlinarith only [HU.2, H, hηhi]
  have hw : |z 3| ≤ 1 / 400 := by
    have HB' : B * b ≤ α ^ 2 / 10000 := HB.trans (div_le_div_of_nonneg_right
      (pow_le_pow_of_le_one hα.1.le hα.2 (by omega : 2 ≤ 2 * J)) (by norm_num))
    apply HW.2.trans
    apply (div_le_iff₀ (sq_pos_of_pos hα.1)).mpr
    nlinarith only [HB', sq_nonneg α]
  have Hrad := HK z hm hu hw
  refine ⟨HV, Hreg, ContDiffAt.comp (g := entranceRadialCoordinates) (f := terminalCyclicInput h) Y
    Hrad.1 Hreg, Hder.trans (div_le_div_of_nonneg_right hscale (sq_nonneg α)), ?_,
    Hlog.trans (div_le_div_of_nonneg_right hscale hα.1.le)⟩
  change ‖fderiv ℝ (entranceRadialCoordinates ∘ terminalCyclicInput h) Y‖ ≤ _
  rw [fderiv_comp Y (Hrad.1.differentiableAt (by norm_num)) (Hreg.differentiableAt (by norm_num))]
  exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul Hrad.2 Hder (norm_nonneg _) hK0)).trans_eq (by ring)
