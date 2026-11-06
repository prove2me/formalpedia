-- Prove2me | solution 1 for BianchiIX.exists_terminal_single_reciprocal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:33:17.490858+00:00
-- url     : https://prove2.me/submissions/d3722437-b74a-4ef0-8733-cb687ac0b03e

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_terminalWallFactor_bounds_uniform
import Theorems.Thm_BianchiIX_exists_terminal_single_correction_bounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Mul

noncomputable section
open BianchiIX



/-- The stable reciprocal correction has the precise old-wall numerator used in (D.31). -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ ≤ 1 / 40000)
    {J : ℕ} (hJ : 2 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η ≤ 1 / 40000 → (0 < α ∧ α ≤ 1) →
      0 < b → b ≤ ε * α ^ (2 * J) → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (terminalSingleReciprocalError h) Y ∧
        |terminalSingleReciprocalError h Y| ≤ C * (|u| * (h + b) + w ^ 2) / α ∧
        |fderiv ℝ (terminalSingleReciprocalError h) Y (Pi.single 0 1)| ≤
          C * (|u| * (h + b) + w ^ 2) / α ^ 2 := by
  obtain ⟨A, hA, εa, hεa, HA⟩ := exists_terminal_single_correction_bounds hη₀ hJ
  obtain ⟨M, hM, εm, hεm, HM⟩ := exists_terminalWallFactor_bounds_uniform
    ⟨hη₀.1, hη₀.2.trans (by norm_num)⟩ hJ
  have hA0 : 0 ≤ A := (by norm_num : (0 : ℝ) ≤ 1).trans hA
  have hM0 : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans hM
  have hC : 1 ≤ 2 * A * M ^ 2 := by nlinarith only [hA, hM, sq_nonneg (M - 1)]
  refine ⟨2 * A * M ^ 2, hC, min εa εm, lt_min hεa hεm, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h
  have hα0 := hα.1
  have hη0 := hη₀.1.trans_le hηlo
  have hsa := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εa εm) (pow_nonneg hα.1.le _))
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εa εm) (pow_nonneg hα.1.le _))
  obtain ⟨HV, _, Hreg, _, _, H0, HD⟩ := HA η α b u w hηlo hηhi hα hb hsa hsum
  obtain ⟨_, Hvfac, Hwfac, Hu, _, HB⟩ := HM η α b u w hηlo (hηhi.trans (by norm_num)) hα hb hsm hsum
  let z := terminalCyclicInput h Y
  change z 2 = w * terminalWallFactor h Y 1 at Hvfac
  change z 3 = u * terminalWallFactor h Y 0 at Hwfac
  change η / 2 * α ^ (J - 2) ≤ z 1 ∧ z 1 ≤ 2 * η * α ^ (J - 2) at Hu
  have hz1 : 0 ≤ z 1 := (by positivity : 0 ≤ η / 2 * α ^ (J - 2)).trans Hu.1
  have Hu' : |z 1| ≤ 2 * h / α ^ 2 := by
    rw [abs_of_nonneg hz1]
    have HP : α ^ J = α ^ (J - 2) * α ^ 2 := by rw [← pow_add]; congr 1; omega
    refine Hu.2.trans_eq ?_
    dsimp only [h]
    rw [HP]
    field_simp
  have Hwall (i : Fin 2) (a : ℝ) : |a * terminalWallFactor h Y i| ≤ M * |a| / α ^ 2 := by
    rw [abs_mul, abs_of_pos (HB i).1]
    exact (mul_le_mul_of_nonneg_left (HB i).2.2.2.1 (abs_nonneg a)).trans_eq (by ring)
  have Hv : |z 2| ≤ M * |w| / α ^ 2 := by rw [Hvfac]; exact Hwall 1 w
  have Hw : |z 3| ≤ M * |u| / α ^ 2 := by rw [Hwfac]; exact Hwall 0 u
  have huB : |u| ≤ b := (le_add_of_nonneg_right (abs_nonneg w)).trans hsum
  let N := |u| * (h + b) + w ^ 2
  have HE : |z 3| * (|z 1| + |z 3|) + (z 2) ^ 2 ≤ 2 * M ^ 2 * N / α ^ 4 := by
    have HV2 : (z 2) ^ 2 ≤ (M * |w| / α ^ 2) ^ 2 := by
      have H := pow_le_pow_left₀ (abs_nonneg (z 2)) Hv 2
      simpa only [sq_abs] using H
    calc
      _ ≤ (M * |u| / α ^ 2) * (2 * h / α ^ 2 + M * |u| / α ^ 2) +
          (M * |w| / α ^ 2) ^ 2 := add_le_add
            (mul_le_mul Hw (add_le_add Hu' Hw) (by positivity) (by positivity)) HV2
      _ = (2 * M * |u| * h + M ^ 2 * |u| ^ 2 + M ^ 2 * w ^ 2) / α ^ 4 := by
        rw [div_pow, sq_abs]
        field_simp
        ring_nf
        simp only [sq_abs]
        ring
      _ ≤ _ := by
        apply (div_le_div_iff_of_pos_right (pow_pos hα.1 4)).mpr
        have Huh := mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ 2 * M * |u| * h)
        have Hub := mul_le_mul_of_nonneg_left huB (by positivity : 0 ≤ M ^ 2 * |u|)
        dsimp only [N]
        nlinarith only [Huh, Hub, (by positivity : 0 ≤ M ^ 2 * |u| * b), (by positivity : 0 ≤ M ^ 2 * w ^ 2)]
  refine ⟨HV, Hreg, ?_, ?_⟩
  · calc
      _ ≤ A * α ^ 3 * (|z 3| * (|z 1| + |z 3|) + (z 2) ^ 2) := H0
      _ ≤ A * α ^ 3 * (2 * M ^ 2 * N / α ^ 4) := mul_le_mul_of_nonneg_left HE (by positivity)
      _ = _ := by field_simp; ring
  · calc
      _ ≤ A * α ^ 2 * (|z 3| * (|z 1| + |z 3|) + (z 2) ^ 2) := HD
      _ ≤ A * α ^ 2 * (2 * M ^ 2 * N / α ^ 4) := mul_le_mul_of_nonneg_left HE (by positivity)
      _ = _ := by field_simp; ring
