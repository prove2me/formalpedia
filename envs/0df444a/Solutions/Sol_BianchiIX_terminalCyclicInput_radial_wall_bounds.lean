-- Prove2me | solution 1 for BianchiIX.terminalCyclicInput_radial_wall_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:39:01.233214+00:00
-- url     : https://prove2.me/submissions/f028bd1d-e490-4990-894a-826a14be2ee0

import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_terminalEntranceInput_fderiv
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
open Filter
open scoped Topology



theorem solution {h α D : ℝ} {Y : ExitTailState}
    (hR : 1 < Y 0) (HV : coreTailValid h Y) (hh : 0 < h)
    (hH : 0 < projectiveCycleDenom (coreTailState h Y))
    (hc : ContDiffAt ℝ 2 (terminalCyclicInput h) Y)
    (hi : ContDiffAt ℝ 2 (terminalEntranceInput h) Y)
    (hlog : ‖fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y‖ ≤ D / α)
    (hlogB : ∀ i : Fin 2, ‖fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z i)) Y‖ ≤ D / α) :
    ∀ i : Fin 4, i ≠ 0 →
      |fderiv ℝ (terminalCyclicInput h) Y (Pi.single 0 1) i| ≤ D * |terminalCyclicInput h Y i| / α := by
  have HD := terminalEntranceInput_fderiv hR HV hh hH hi (Pi.single 0 1)
  have Hlog (L : ExitTailState →L[ℝ] ℝ) (H : ‖L‖ ≤ D / α) : |L (Pi.single 0 1)| ≤ D / α := by
    simpa only [Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] using
      (L.le_opNorm (Pi.single 0 1)).trans (mul_le_mul_of_nonneg_right H (norm_nonneg _))
  have Heq (i : Fin 4) (hi0 : i ≠ 0) :
      fderiv ℝ (terminalCyclicInput h) Y (Pi.single 0 1) i =
        fderiv ℝ (terminalEntranceInput h) Y (Pi.single 0 1) i := by
    have HE : (fun Z => terminalCyclicInput h Z i) = (fun Z => terminalEntranceInput h Z i) := by
      fin_cases i
      · exact False.elim (hi0 rfl)
      all_goals rfl
    have Hc := fderiv_apply (hc.differentiableAt (by norm_num)) i
    have Hi := fderiv_apply (hi.differentiableAt (by norm_num)) i
    rw [HE] at Hc
    exact congrArg (fun L : ExitTailState →L[ℝ] ℝ => L (Pi.single 0 1)) (Hc.symm.trans Hi)
  intro i hi0
  rw [Heq i hi0, HD]
  fin_cases i
  · exact False.elim (hi0 rfl)
  all_goals simp only [Pi.single_eq_of_ne (by decide : (1 : Fin 3) ≠ 0),
    Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0), zero_mul, zero_add]
  · change |terminalEntranceInput h Y 1 *
      fderiv ℝ (fun Z => Real.log (terminalEntranceInput h Z 1)) Y (Pi.single 0 1)| ≤
        D * |terminalEntranceInput h Y 1| / α
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Hlog _ hlog) (abs_nonneg _)).trans_eq (by ring)
  · change |terminalEntranceInput h Y 2 *
      fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 1)) Y (Pi.single 0 1)| ≤
        D * |terminalEntranceInput h Y 2| / α
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Hlog _ (hlogB 1)) (abs_nonneg _)).trans_eq (by ring)
  · change |terminalEntranceInput h Y 3 *
      fderiv ℝ (fun Z => Real.log (terminalWallFactor h Z 0)) Y (Pi.single 0 1)| ≤
        D * |terminalEntranceInput h Y 3| / α
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Hlog _ (hlogB 0)) (abs_nonneg _)).trans_eq (by ring)
