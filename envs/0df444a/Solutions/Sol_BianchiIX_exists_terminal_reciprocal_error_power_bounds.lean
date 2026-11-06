-- Prove2me | solution 1 for BianchiIX.exists_terminal_reciprocal_error_power_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:33:28.525617+00:00
-- url     : https://prove2.me/submissions/f25aca0d-1df1-4b60-a40d-a0192b9c6c07

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_terminalWallFactor_bounds_uniform
import Theorems.Thm_BianchiIX_exists_terminal_reciprocal_error_bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Topology.Instances.Real.Lemmas
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
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open BianchiIX



/-- The powers in (D.30) come from the actual wall factors and hold uniformly in the auxiliary height. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 1000 ∧ ∀ η₀ : ℝ, (0 < η₀ ∧ η₀ ≤ δ) →
      ∀ J : ℕ, 4 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ δ → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b → 0 < u → 0 < w →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalReciprocalError h) Y ∧
        1 / α ≤ terminalConnectionPhase h Y ∧ 1 / α ≤ terminalEntranceInput h Y 0 ∧
        |terminalReciprocalError h Y| ≤ C * w * α ^ (J - 1) ∧
        (|fderiv ℝ (terminalReciprocalError h) Y (Pi.single 0 1)| +
          |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 1 1)| ≤ C * w * α ^ (J - 4)) ∧
        |fderiv ℝ (terminalReciprocalError h) Y (Pi.single 2 1)| ≤ C * α ^ (J - 2) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_reciprocal_error_bounds
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η₀ hη₀ J hJ
  have hJ2 : 2 ≤ J := by omega
  obtain ⟨A, hA, εe, hεe, HA⟩ := HE η₀ hη₀ J hJ2
  have hη₀100 : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, (hη₀.2.trans hδhi).trans (by norm_num)⟩
  obtain ⟨M, hM, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform hη₀100 hJ2
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hAM : A ≤ A * M := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hM hA0
  refine ⟨A * M, hA.trans hAM, min εe εm, lt_min hεe hεm, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum hu hw Y h
  have hη100 : η ≤ 1 / 100 := (hηhi.trans hδhi).trans (by norm_num)
  have hη2 : 2 * η ≤ 1 := by linarith only [hηhi.trans hδhi]
  have hα0 := hα.1
  have hse := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εe εm) (pow_nonneg hα.1.le (2 * J)))
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εe εm) (pow_nonneg hα.1.le (2 * J)))
  obtain ⟨HV, Hreg, HF, HR, H0, H01, H2⟩ := HA η α b u w hηlo hηhi hα hb hse hsum hu hw
  obtain ⟨_, Hfactor, _, HU, _, HB⟩ := HM η α b u w hηlo hη100 hα hb hsm hsum
  let z := terminalEntranceInput h Y
  change z 2 = w * terminalWallFactor h Y 1 at Hfactor
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at HU
  have hU : z 1 ≤ α ^ (J - 2) := HU.2.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hη2 (pow_nonneg hα.1.le (J - 2)))
  have hV0 : 0 ≤ z 2 := by rw [Hfactor]; exact mul_nonneg hw.le (HB 1).1.le
  have hV : z 2 ≤ M * w / α ^ 2 := by
    rw [Hfactor]
    exact (mul_le_mul_of_nonneg_left (HB 1).2.2.2.1 hw.le).trans_eq (by ring)
  have hp4 : α ^ (J - 2) = α ^ (J - 4) * α ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  have hprod : z 1 * z 2 ≤ M * w * α ^ (J - 4) := by
    calc
      _ ≤ α ^ (J - 2) * (M * w / α ^ 2) := mul_le_mul hU hV hV0 (pow_nonneg hα.1.le (J - 2))
      _ = _ := by rw [hp4]; field_simp [hα.1.ne']
  have hp1 : α ^ (J - 4) * α ^ 3 = α ^ (J - 1) := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨HV, Hreg, HF, HR, ?_, ?_, ?_⟩
  · calc
      _ ≤ A * α ^ 3 * z 1 * z 2 := H0
      _ = (A * α ^ 3) * (z 1 * z 2) := by ring
      _ ≤ (A * α ^ 3) * (M * w * α ^ (J - 4)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (A * M) * w * (α ^ (J - 4) * α ^ 3) := by ring
      _ = _ := by rw [hp1]
  · calc
      _ ≤ A * z 1 * z 2 := H01
      _ = A * (z 1 * z 2) := by ring
      _ ≤ A * (M * w * α ^ (J - 4)) := mul_le_mul_of_nonneg_left hprod hA0
      _ = _ := by ring
  · exact H2.trans ((mul_le_mul_of_nonneg_left hU hA0).trans
      (mul_le_mul_of_nonneg_right hAM (pow_nonneg hα.1.le (J - 2))))
