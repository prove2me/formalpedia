-- Prove2me | solution 1 for BianchiIX.exists_era_time_regular
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T03:35:37.979886+00:00
-- url     : https://prove2.me/submissions/1514c6a0-1abd-4fd0-8e0e-021ca855d12d

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
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_core_itinerary
import Theorems.Thm_BianchiIX_exists_era_bounded_phase_estimates
import Theorems.Thm_BianchiIX_exists_reflectionReturn_phase_bounds
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



/-- Every finite core-block time is locally C1 on the same phase-margin domains, uniformly in the number of cores. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∃ ε > (0 : ℝ), ∃ C ≥ (1 : ℝ),
      ∀ (m : ℕ) (β : ℝ) (X : CoreAngleState), 0 < β → β < 1 / 2 →
        (0 < X 1 ∧ X 1 ≤ ε / X 0) → (0 < X 2 ∧ X 2 ≤ ε / X 0) →
        X 1 + X 2 ≤ ε * (β / 2) ^ (2 * J) →
        ((m : ℝ) + 1 + β ≤ X 0 / 2 ∧ X 0 / 2 ≤ (m : ℝ) + 2 - β) →
        C * (X 1 + X 2) < β / 4 → ContDiffAt ℝ 1 (eraReturnTime η J m) X := by
  obtain ⟨δ, hδ, hδmax, HP⟩ := exists_era_bounded_phase_estimates
  obtain ⟨εK, hεK, _, K, hK, HK⟩ := exists_core_itinerary
  obtain ⟨εR, hεR, _, _, _, HR⟩ := exists_reflectionReturn_phase_bounds
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ
  obtain ⟨εP, hεP, _, CP, hCP, Hp⟩ := HP η hη hηδ J hJ
  let ε := min εP (min εK (εR / 4))
  let C := max CP K
  have hε : 0 < ε := lt_min hεP (lt_min hεK (div_pos hεR (by norm_num)))
  have hεP' : ε ≤ εP := min_le_left _ _
  have hεK' : ε ≤ εK := (min_le_right _ _).trans (min_le_left _ _)
  have hεR' : ε ≤ εR / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hC : 1 ≤ C := hCP.trans (le_max_left _ _)
  refine ⟨ε, hε, C, hC, ?_⟩
  intro m β X hβ hβmax hu hw hsmall hphase hmargin
  let F := coreReturnState coreRadiusReturnTime
  let G := coreReflectionState coreRadiusReturnTime
  let b := X 1 + X 2
  have hb : 0 < b := add_pos hu.1 hw.1
  have hX : 2 < X 0 := by nlinarith only [hphase.1, hβ, Nat.cast_nonneg (α := ℝ) m]
  have hX0 : 0 < X 0 := lt_trans (by norm_num) hX
  have hscale {e : ℝ} (he : ε ≤ e) : ε / X 0 ≤ e / X 0 :=
    div_le_div_of_nonneg_right he hX0.le
  have hbound {c : ℝ} (hc : c ≤ C) : c * b < β / 4 :=
    (mul_le_mul_of_nonneg_right hc hb.le).trans_lt hmargin
  obtain ⟨Hall, Hconn, _, _, _⟩ := HK m β X hβ hβmax
    ⟨hu.1, hu.2.trans (hscale hεK')⟩ ⟨hw.1, hw.2.trans (hscale hεK')⟩ hphase
    ((hbound (le_max_right _ _)).trans (by linarith only [hβ]))
  obtain ⟨_, _, Hterminal, _⟩ := Hp m β X hβ hβmax
    ⟨hu.1, hu.2.trans (hscale hεP')⟩ ⟨hw.1, hw.2.trans (hscale hεP')⟩
    (hsmall.trans (mul_le_mul_of_nonneg_right hεP' (pow_nonneg (half_pos hβ).le _)))
    hphase (hbound (le_max_left _ _))
  have hbX : b * X 0 ≤ 2 * ε := by
    have hU := (le_div_iff₀ hX0).mp hu.2
    have hW := (le_div_iff₀ hX0).mp hw.2
    dsimp only [b]
    nlinarith only [hU, hW]
  have Hreflection (j : ℕ) (hj : j < m) :
      ContDiffAt ℝ 1 (coreReflectionTime ∘ G^[j]) X := by
    obtain ⟨_, _, _, HF, HT, Hz, Hsum, Herr, _⟩ := Hall j hj.le
    let Z := F (G^[j] X)
    have hZ4 : 31 / 8 ≤ Z 0 := by linarith only [(Hconn j hj).1, hβ]
    have hZ0 : 0 < Z 0 := lt_of_lt_of_le (by norm_num) hZ4
    have hZupper : Z 0 ≤ 2 * X 0 := by
      have he : |Z 0 - (X 0 - 2 * j)| < β / 4 :=
        ((le_add_of_nonneg_left (abs_nonneg _)).trans Herr).trans_lt (hbound (le_max_right _ _))
      nlinarith only [(abs_lt.mp he).2, hβmax, hX, Nat.cast_nonneg (α := ℝ) j]
    have hsmallZ (i : Fin 2) : 0 < Z i.succ ∧ Z i.succ ≤ εR / Z 0 := by
      have hZi := Hz i
      have hZb : Z i.succ ≤ b := by
        fin_cases i
        · exact (le_add_of_nonneg_right (Hz 1).le).trans Hsum
        · exact (le_add_of_nonneg_left (Hz 0).le).trans Hsum
      refine ⟨hZi, (le_div_iff₀ hZ0).mpr ?_⟩
      calc
        _ ≤ b * Z 0 := mul_le_mul_of_nonneg_right hZb hZ0.le
        _ ≤ b * (2 * X 0) := mul_le_mul_of_nonneg_left hZupper hb.le
        _ ≤ εR := by nlinarith only [hbX, hεR']
    obtain ⟨_, _, Hτ, _⟩ := HR Z hZ4 (hsmallZ 0) (hsmallZ 1)
    change ContDiffAt ℝ 1 (fun Y => reflectionReturnTime (F (G^[j] Y)) + coreRadiusReturnTime (G^[j] Y)) X
    exact ((Hτ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).comp X HF).add HT
  have Hprefix : ContDiffAt ℝ 1 (corePrefixTime m) X := by
    apply ContDiffAt.sum
    intro j hj
    exact Hreflection j (Finset.mem_range.mp hj)
  exact Hterminal.add ((Hall m le_rfl).2.2.2.2.1.add Hprefix)
