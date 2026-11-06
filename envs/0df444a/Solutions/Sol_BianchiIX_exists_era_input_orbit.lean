-- Prove2me | solution 1 for BianchiIX.exists_era_input_orbit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:39:45.206402+00:00
-- url     : https://prove2.me/submissions/1629de4c-b4d3-4e7c-9a9f-dddeddb2c697

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_eraReturn_normalized_endpoint
import Theorems.Thm_BianchiIX_exists_era_bounded_phase_estimates
import Theorems.Thm_BianchiIX_exists_era_input_avoidance
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
open BianchiIX
open Set



/-- Every retained input has the explicitly summed positive return time and the exact physical endpoint in its accumulated axis frame. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bstar m,
          0 < eraReturnTime η J m p.2 ∧
          eraReturnTime η J m p.2 ∈ normalizedMaxDomain (fromProjectiveState (coreRadiusEntry p.2)) 0 ∧
          fromProjectiveState (coreRadiusEntry (eraNextState η J m p.2)) =
            (axisFrame (eraReturnFrame m)).map (normalizedMaxCurve
              (fromProjectiveState (coreRadiusEntry p.2)) 0 (eraReturnTime η J m p.2)) ∧
          coreRadiusReturnValid p.2 ∧ Nat.floor (p.2 0 / 2) = m + 1 := by
  obtain ⟨δp, hδp, hδmax, HP⟩ := exists_era_bounded_phase_estimates
  obtain ⟨δa, hδa, _, HA⟩ := exists_era_input_avoidance
  refine ⟨min δp δa, lt_min hδp hδa, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨a, ha, _, C, hC, Hp⟩ := HP η hη (hηδ.trans (min_le_left _ _)) J (by omega)
  obtain ⟨Ba, hBa, _, Ha⟩ := HA η hη (hηδ.trans (min_le_right _ _)) J hJ σ hσ hσone hσJ
  obtain ⟨Br, hBr, hBrone, Hr⟩ := exists_retained_era_parameter_budget ha
    (le_trans zero_le_one hC) hσ hσone hσJ
  refine ⟨min Br Ba, lt_min hBr hBa, (min_le_left _ _).trans_lt hBrone, ?_⟩
  intro m p hp
  obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
  obtain ⟨_, _, _, _, hrec, _⟩ := Ha m p ⟨⟨hB.1, hB.2.trans (min_le_right _ _)⟩, hm, hu, hw, hsum, hr⟩
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := Hr p.1 ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  have hcap : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have hrpos : 0 < p.2 0 := by nlinarith only [hr.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hBrX : p.1 * p.2 0 ≤ a :=
    (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hcap)
  have hwall {z : ℝ} (hz : z ≤ p.1) : z ≤ a / p.2 0 :=
    (le_div_iff₀ hrpos).mpr ((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBrX)
  have hphase : (m : ℝ) + 1 + p.1 ^ σ ≤ p.2 0 / 2 ∧ p.2 0 / 2 ≤ (m : ℝ) + 2 - p.1 ^ σ := by
    constructor <;> linarith only [hr.1, hr.2]
  obtain ⟨_, _, _, _, _, _, hcount, _, Hvalid, Hconn, _, hchart, Hfirst, Hactual, Hunit, _, _⟩ :=
    Hp m (p.1 ^ σ) p.2 hβ (by linarith only [hβmax])
      ⟨hu, hwall (by linarith only [hsum, hw])⟩ ⟨hw, hwall (by linarith only [hsum, hu])⟩
      (hsum.trans hsmall) hphase
      ((mul_le_mul_of_nonneg_left hsum (le_trans zero_le_one hC)).trans_lt hmargin)
  obtain ⟨hT, hdom, hend⟩ := eraReturn_normalized_endpoint Hvalid
    (fun j hj => (Hconn j hj).2) hchart Hfirst.1.1 Hactual Hunit
  refine ⟨hT, hdom, ?_, Hvalid 0 (Nat.zero_le _), hcount⟩
  rw [hrec]
  exact hend
