-- Prove2me | solution 1 for BianchiIX.exists_era_input_estimates
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:36:22.288674+00:00
-- url     : https://prove2.me/submissions/9a47551f-4bc2-4883-8740-189bbd2ce3ca

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_era_bounded_phase_estimates
import Theorems.Thm_BianchiIX_exists_era_output_estimates
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
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



/-- Uniform phase and amplitude bounds hold before imposing selection on the output phase. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ C ≥ (1 : ℝ), ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          ∀ m : ℕ, ∀ p ∈ eraInputSelection σ Bstar m,
            |2 / eraOutputRadius η J m p.2 - (p.2 0 / 2 - ((m : ℝ) + 1))| ≤ C * p.1 ∧
            C * p.1 < p.1 ^ σ / 4 ∧
            0 < eraNextState η J m p.2 1 ∧ 0 < eraNextState η J m p.2 2 ∧
            eraNextState η J m p.2 1 + eraNextState η J m p.2 2 ≤ p.1 ^ (4 / 3 : ℝ) ∧
            ∀ j ≤ m, coreRadiusReturnValid ((coreReflectionState coreRadiusReturnTime)^[j] p.2) := by
  obtain ⟨δp, hδp, hδmax, HP⟩ := exists_era_bounded_phase_estimates
  obtain ⟨δo, hδo, _, HO⟩ := exists_era_output_estimates
  refine ⟨min δp δo, lt_min hδp hδo, (min_le_left _ _).trans hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨εp, hεp, _, Cp, hCp, Hp⟩ := HP η hη (hηδ.trans (min_le_left _ _)) J (by omega)
  obtain ⟨εo, hεo, _, Co, hCo, Ho⟩ := HO η hη (hηδ.trans (min_le_right _ _)) J hJ
  let ε := min εp εo
  let C := max Cp Co
  have hC : 1 ≤ C := hCp.trans (le_max_left _ _)
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  obtain ⟨Br, hBr, hBrone, Hr⟩ := exists_retained_era_parameter_budget (lt_min hεp hεo)
    hC0 hσ hσone hσJ
  obtain ⟨Ba, hBa, _, Ha⟩ := exists_common_rpow_budget (ι := Fin 1) Finset.univ
    (C := fun _ => C) (p := fun _ => 17 / 30) (ε := fun _ => 1)
    (by intros; exact hC0) (by intros; norm_num) (by intros; norm_num)
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨C, hC, min Br Ba, lt_min hBr hBa, (min_le_left _ _).trans_lt hBrone, ?_⟩
  intro m p hp
  obtain ⟨hB, hm, hu, hw, hsum, hr⟩ := hp
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := Hr p.1 ⟨hB.1, hB.2.trans (min_le_left _ _)⟩
  have hcap : (m : ℝ) + 1 ≤ 1 / p.1 ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / p.1 ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have hrpos : 0 < p.2 0 := by nlinarith only [hr.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hBrX : p.1 * p.2 0 ≤ ε :=
    (mul_le_mul_of_nonneg_left hr.2 hB.1.le).trans (hscale m hcap)
  have hwall {z e : ℝ} (hz : z ≤ p.1) (he : ε ≤ e) : z ≤ e / p.2 0 :=
    (le_div_iff₀ hrpos).mpr (((mul_le_mul_of_nonneg_right hz hrpos.le).trans hBrX).trans he)
  have hphase : (m : ℝ) + 1 + p.1 ^ σ ≤ p.2 0 / 2 ∧ p.2 0 / 2 ≤ (m : ℝ) + 2 - p.1 ^ σ := by
    constructor <;> linarith only [hr.1, hr.2]
  have hsmall' {e : ℝ} (he : ε ≤ e) : p.2 1 + p.2 2 ≤ e * (p.1 ^ σ / 2) ^ (2 * J) :=
    hsum.trans (hsmall.trans (mul_le_mul_of_nonneg_right he (pow_nonneg (half_pos hβ).le _)))
  have hmargin' {c : ℝ} (hc : c ≤ C) : c * (p.2 1 + p.2 2) < p.1 ^ σ / 4 :=
    ((mul_le_mul_of_nonneg_right hc (add_pos hu hw).le).trans
      (mul_le_mul_of_nonneg_left hsum hC0)).trans_lt hmargin
  obtain ⟨_, _, _, _, _, Hphase, _, _, Hvalid, _⟩ := Hp m (p.1 ^ σ) p.2 hβ (by linarith only [hβmax])
    ⟨hu, hwall (by linarith only [hsum, hw]) (min_le_left _ _)⟩
    ⟨hw, hwall (by linarith only [hsum, hu]) (min_le_left _ _)⟩
    (hsmall' (min_le_left _ _)) hphase (hmargin' (le_max_left _ _))
  obtain ⟨_, _, hU, hW, Hamp, _⟩ := Ho m (p.1 ^ σ) p.2 hβ (by linarith only [hβmax])
    ⟨hu, hwall (by linarith only [hsum, hw]) (min_le_right _ _)⟩
    ⟨hw, hwall (by linarith only [hsum, hu]) (min_le_right _ _)⟩
    (hsmall' (min_le_right _ _)) hphase (hmargin' (le_max_right _ _))
  change |2 / eraOutputRadius η J m p.2 - (p.2 0 / 2 - ((m : ℝ) + 1))| ≤ Cp * (p.2 1 + p.2 2) at Hphase
  refine ⟨Hphase.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (add_pos hu hw).le).trans
    (mul_le_mul_of_nonneg_left hsum hC0)), hmargin, hU, hW, ?_, Hvalid⟩
  change eraOutputState η J m p.2 1 + eraOutputState η J m p.2 3 ≤ p.1 ^ (4 / 3 : ℝ)
  have hfactor : p.1 ^ (19 / 10 : ℝ) = p.1 ^ (17 / 30 : ℝ) * p.1 ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_add hB.1]
    norm_num
  calc
    _ ≤ Co * (p.2 1 + p.2 2) ^ (19 / 10 : ℝ) := Hamp
    _ ≤ C * p.1 ^ (19 / 10 : ℝ) := mul_le_mul (le_max_right _ _)
      (Real.rpow_le_rpow (add_pos hu hw).le hsum (by norm_num)) (by positivity) hC0
    _ = (C * p.1 ^ (17 / 30 : ℝ)) * p.1 ^ (4 / 3 : ℝ) := by rw [hfactor]; ring
    _ ≤ 1 * p.1 ^ (4 / 3 : ℝ) := mul_le_mul_of_nonneg_right
      (Ha p.1 ⟨hB.1, hB.2.trans (min_le_right _ _)⟩ 0 (Finset.mem_univ _)).le
      (Real.rpow_nonneg hB.1.le _)
    _ = _ := one_mul _
