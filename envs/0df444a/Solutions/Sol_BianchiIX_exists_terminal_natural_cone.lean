-- Prove2me | solution 1 for BianchiIX.exists_terminal_natural_cone
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:46:50.123326+00:00
-- url     : https://prove2.me/submissions/929a3933-2b42-40d1-81e5-cbba1a279e13

import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_terminal_connection_cone
import Theorems.Thm_BianchiIX_exists_terminal_connection_height_freezing
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



/-- The natural-height terminal map has the same ordinary cone differential as the frozen passage. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 5 ≤ J → ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b U W : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ (2 * J) → |U| + |W| ≤ b → 0 < U → 0 < W →
      let Y : ExitTailState := ![2 + 2 * α, U, W]
      coreTailValid (η * α ^ J) Y ∧ ContDiffAt ℝ 2 (terminalNaturalState η J) Y ∧
        ContDiffAt ℝ 2 (terminalNaturalPhase η J) Y ∧
        0 < terminalNaturalState η J Y 1 ∧ 0 < terminalNaturalState η J Y 3 ∧
        C * b ^ (7 / 24 : ℝ) < 1 / 2 ∧
        ∀ d : ExitTailState, d 0 = 1 → |d 1| ≤ Real.sqrt U → |d 2| ≤ Real.sqrt W →
          let p := fderiv ℝ (terminalNaturalPhase η J) Y d
          p < 0 ∧ 3 / (4 * α ^ 2) ≤ |p| ∧
          max (|fderiv ℝ (terminalNaturalState η J) Y d 1| / (Real.sqrt (terminalNaturalState η J Y 1) * |p|))
            (|fderiv ℝ (terminalNaturalState η J) Y d 3| / (Real.sqrt (terminalNaturalState η J Y 3) * |p|)) ≤
              C * b ^ (7 / 24 : ℝ) := by
  obtain ⟨δ, hδ, hδhi, HE⟩ := exists_terminal_connection_cone
  refine ⟨δ, hδ, hδhi, ?_⟩
  intro η hη hηhi J hJ
  obtain ⟨C, hC, εc, hεc, HC⟩ := HE η ⟨hη, hηhi⟩ J hJ
  have hη100 : η ≤ 1 / 100 := (hηhi.trans hδhi).trans (by norm_num)
  have hbudget : η ≤ (1 / 10000 : ℝ) / (4 * (11 / 5) ^ (0 : ℕ)) := by
    norm_num
    exact hηhi.trans hδhi
  obtain ⟨εh, hεh, HH⟩ := exists_terminal_connection_height_freezing
    (εin := 1 / 10000) (η := η) (q := 0) (J := J)
    (by norm_num) ⟨hη, hη100⟩ (by omega) hbudget
  refine ⟨C, hC, min εc εh, lt_min hεc hεh, ?_⟩
  intro α b U W hα hb hsmall hsum hU hW Y
  let h := η * α ^ J
  have hsc := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εc εh) (pow_nonneg hα.1.le _))
  have hsh := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εc εh) (pow_nonneg hα.1.le _))
  obtain ⟨HV, Hstate, Hphase, HU, HW, Hsmall, Hcone⟩ := HC η α b U W le_rfl hηhi hα hb hsc hsum hU hW
  obtain ⟨_, _, Hfreeze⟩ := HH α b U W hα hb hsh hsum hU hW
  let a := fun Z : ExitTailState => η * ((Z 0 - 2) / 2) ^ J
  have ha : ContinuousAt a Y :=
    ((((continuousAt_apply 0 Y).sub_const 2).div_const 2).pow J).const_mul η
  have hbase : (Y 0 - 2) / 2 = α := by change (2 + 2 * α - 2) / 2 = α; ring
  have haY : a Y = h := by dsimp only [a]; rw [hbase]
  have Hnear := (Hfreeze a ha haY).1
  have HstateEq : terminalNaturalState η J =ᶠ[𝓝 Y] terminalConnectionState h := by
    filter_upwards [Hnear] with Z hZ
    exact hZ.2
  have HphaseEq : terminalNaturalPhase η J =ᶠ[𝓝 Y] terminalConnectionPhase h := by
    filter_upwards [HstateEq] with Z hZ
    change coreRadius (terminalNaturalState η J Z 0) (terminalNaturalState η J Z 2) = _
    rw [hZ]
    rfl
  have Hvalue := HstateEq.self_of_nhds
  refine ⟨HV, Hstate.congr_of_eventuallyEq HstateEq, Hphase.congr_of_eventuallyEq HphaseEq,
    ?_, ?_, Hsmall, ?_⟩
  · rw [Hvalue]
    exact HU
  · rw [Hvalue]
    exact HW
  · intro d hd0 hd1 hd2 p
    dsimp only [p]
    rw [HstateEq.fderiv_eq, HphaseEq.fderiv_eq, Hvalue]
    exact Hcone d hd0 hd1 hd2
