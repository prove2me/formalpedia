-- Prove2me | solution 1 for BianchiIX.exists_terminalConnection_sqrt_bounds_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:27:42.152278+00:00
-- url     : https://prove2.me/submissions/03cc581c-ec06-42f9-8122-835fdca4e2bd

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_EntranceReturn
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_entranceReturn_decay
import Theorems.Thm_BianchiIX_exists_terminalWallFactor_bounds_uniform
import Theorems.Thm_BianchiIX_exists_terminal_cycle_entrance_inputs_uniform
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

noncomputable section
open BianchiIX

private theorem BianchiIX.entranceReturn_sqrt_decay {y : ProjectiveState}
    (hk : 7 / 4 ≤ coreRadius (y 0) (y 2)) (hm : 1 ≤ y 0)
    (hu : 0 ≤ y 1 ∧ y 1 ≤ 1 / 10000) (hv : 0 < y 2 ∧ y 2 < 1)
    (hw : 0 ≤ y 3 ∧ y 3 ≤ 1 / 10000) :
    Real.sqrt (entranceReturnState y 1) ≤ Real.sqrt (y 1) * (y 2) ^ (19 / 24 : ℝ) ∧
      Real.sqrt (entranceReturnState y 3) ≤ Real.sqrt (y 3) * Real.sqrt (y 2) := by
  have H := entranceReturn_decay hk hm hu hv hw
  have hk0 : 0 < coreRadius (y 0) (y 2) := by linarith only [hk]
  have hlog : Real.log (y 2) ≤ 0 := Real.log_nonpos hv.1.le hv.2.le
  have hexp : y 2 * Real.exp (-coreRadius (y 0) (y 2) * -Real.log (y 2) / 3) ≤
      (y 2) ^ (19 / 12 : ℝ) := by
    conv_lhs => lhs; rw [← Real.exp_log hv.1]
    rw [← Real.exp_add, Real.rpow_def_of_pos hv.1]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hk) hlog]
  have HU : entranceReturnState y 1 ≤ y 1 * (y 2) ^ (19 / 12 : ℝ) :=
    H.1.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hexp hu.1)
  have HW : entranceReturnState y 3 ≤ y 3 * y 2 := H.2.trans (mul_le_of_le_one_right
    (mul_nonneg hw.1 hv.1.le) (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by simpa using hlog) hk0.le)))
  constructor
  · have HS := Real.sqrt_le_sqrt HU
    rw [Real.sqrt_mul hu.1, Real.sqrt_eq_rpow ((y 2) ^ (19 / 12 : ℝ)), ← Real.rpow_mul hv.1.le] at HS
    norm_num at HS
    exact HS
  · simpa only [Real.sqrt_mul hw.1] using Real.sqrt_le_sqrt HW


/-- The actual terminal amplitudes supply every square-root scale needed in (D.37). -/
theorem solution {η₀ : ℝ}
    (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 40000) {J : ℕ} (hJ : 2 ≤ J) :
    ∃ A ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b U W : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |U| + |W| ≤ b → 0 < U → 0 < W →
      let Y : ExitTailState := ![2 + 2 * α, U, W]
      let h := η * α ^ J
      let z := terminalEntranceInput h Y
      (0 < z 2 ∧ z 2 < 1) ∧
        Real.sqrt (z 1) ≤ α ^ (((J : ℝ) - 2) / 2) ∧
        Real.sqrt (z 2) ≤ A / α * Real.sqrt W ∧
        Real.sqrt (z 3) ≤ A / α * Real.sqrt U ∧ z 2 ≤ A * W / α ^ 2 ∧
        Real.sqrt (terminalConnectionState h Y 1) ≤ Real.sqrt (z 1) * (z 2) ^ (19 / 24 : ℝ) ∧
        Real.sqrt (terminalConnectionState h Y 3) ≤ Real.sqrt (z 3) * Real.sqrt (z 2) := by
  have hη₀' : 0 < η₀ ∧ η₀ ≤ 1 / 100 := ⟨hη₀.1, by linarith only [hη₀.2]⟩
  obtain ⟨A, hA, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform hη₀' hJ
  obtain ⟨εi, hεi, HI⟩ := exists_terminal_cycle_entrance_inputs_uniform
    (εin := 1 / 10000) (by norm_num) hη₀' (q := 0) hJ
  have hA0 : 0 ≤ A := le_trans (by norm_num) hA
  have hsA : Real.sqrt A ≤ A := Real.sqrt_le_iff.mpr ⟨hA0, by nlinarith only [hA]⟩
  refine ⟨A, hA, min εm εi, lt_min hεm hεi, ?_⟩
  intro η α b U W hηlo hηhi hα hb hsmall hsum hU hW Y h z
  have hα0 : 0 < α := hα.1
  have hη100 : η ≤ 1 / 100 := by linarith only [hηhi]
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εm εi) (pow_nonneg hα.1.le _))
  have hsi := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εm εi) (pow_nonneg hα.1.le _))
  obtain ⟨_, Hvfac, Hwfac, Hu, _, Hfactor⟩ := HM η α b U W hηlo hη100 hα hb hsm hsum
  obtain ⟨_, _, HK, Hm, HU, HV, HW, _, _⟩ := HI η α b U W hηlo hη100
    (by norm_num; exact hηhi) hα hb hsi hsum hU hW
  let y := terminalCyclicInput h Y
  change z 2 = W * terminalWallFactor h Y 1 at Hvfac
  change z 3 = U * terminalWallFactor h Y 0 at Hwfac
  change 2 < y 0 at Hm
  change 0 < z 2 ∧ z 2 < 1 / 2 at HV
  have hv : 0 < z 2 ∧ z 2 < 1 := ⟨HV.1, by linarith only [HV.2]⟩
  have Hdec := entranceReturn_sqrt_decay HK.le (by linarith only [Hm] : 1 ≤ y 0)
    ⟨HU.1.le, HU.2.1⟩ hv ⟨HW.1.le, HW.2.1⟩
  have hvscale : z 2 ≤ A * W / α ^ 2 := by
    rw [Hvfac]
    exact (mul_le_mul_of_nonneg_left (Hfactor 1).2.2.2.1 hW.le).trans_eq (by ring)
  have hwscale : z 3 ≤ A * U / α ^ 2 := by
    rw [Hwfac]
    exact (mul_le_mul_of_nonneg_left (Hfactor 0).2.2.2.1 hU.le).trans_eq (by ring)
  have hroot {a x : ℝ} (hx : 0 ≤ x) (H : a ≤ A * x / α ^ 2) :
      Real.sqrt a ≤ A / α * Real.sqrt x := by
    have HS := Real.sqrt_le_sqrt H
    rw [Real.sqrt_div (mul_nonneg hA0 hx), Real.sqrt_mul hA0, Real.sqrt_sq hα.1.le] at HS
    exact HS.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsA (Real.sqrt_nonneg x)) hα.1.le).trans_eq (by ring))
  refine ⟨hv, ?_, hroot hW.le hvscale, hroot hU.le hwscale, hvscale, Hdec⟩
  have HUscale : z 1 ≤ α ^ (J - 2) := Hu.2.trans (mul_le_of_le_one_left
    (pow_nonneg hα.1.le _) (by linarith only [hηhi] : 2 * η ≤ 1))
  have HS := Real.sqrt_le_sqrt HUscale
  rw [Real.sqrt_eq_rpow (α ^ (J - 2)), ← Real.rpow_natCast α (J - 2), ← Real.rpow_mul hα.1.le] at HS
  have hcast : ((J - 2 : ℕ) : ℝ) = (J : ℝ) - 2 := by rw [Nat.cast_sub hJ]; norm_num
  rw [hcast] at HS
  rw [show ((J : ℝ) - 2) * (1 / 2) = ((J : ℝ) - 2) / 2 by ring] at HS
  exact HS
