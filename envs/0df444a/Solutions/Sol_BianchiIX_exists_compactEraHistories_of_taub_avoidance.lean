-- Prove2me | solution 1 for BianchiIX.exists_compactEraHistories_of_taub_avoidance
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:14:50.164662+00:00
-- url     : https://prove2.me/submissions/77a3d7cd-0c88-4217-9f90-3d273976365b

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_exists_compactEraPhase_of_taub_avoidance
import Theorems.Thm_BianchiIX_exists_era_input_avoidance
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
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
open BianchiIX
open Set



/-- A physically Taub-avoiding small core has compact phase along every selected finite history. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∃ γ > (0 : ℝ), γ < 1 / 4 ∧
          ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ Bcap : ℝ, ∀ p : ℝ × CoreAngleState,
            p.1 ∈ Ioc 0 Bstar → 2 - γ / 2 ≤ p.2 0 →
            0 < p.2 1 → 0 < p.2 2 → p.2 1 + p.2 2 ≤ p.1 →
            normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry p.2)) →
            compactEraHistories η J σ Bcap N γ p := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_input_avoidance
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ ε hε
  obtain ⟨Be, hBe, hBeone, He⟩ := H η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨N, γ, hγ, hγmax, Bc, hBc, Hc⟩ := exists_compactEraPhase_of_taub_avoidance hε
  let Bstar := min Be Bc
  have hBstar : 0 < Bstar := lt_min hBe hBc
  have hBBe : Bstar ≤ Be := min_le_left _ _
  have hBBc : Bstar ≤ Bc := min_le_right _ _
  have hBone : Bstar < 1 := hBBe.trans_lt hBeone
  refine ⟨N, γ, hγ, hγmax, Bstar, hBstar, hBone, ?_⟩
  intro Bcap
  have Hhistory : ∀ w : List ℕ+, ∀ p : ℝ × CoreAngleState,
      p.1 ∈ Ioc 0 Bstar → 2 - γ / 2 ≤ p.2 0 →
      0 < p.2 1 → 0 < p.2 2 → p.2 1 + p.2 2 ≤ p.1 →
      normalizedTaubAvoidance ε (fromProjectiveState (coreRadiusEntry p.2)) →
      p ∈ eraPrefixDomain η J σ Bcap w →
      (eraPrefixState η J w p).2 ∈ compactEraPhase N γ := by
    intro w
    induction w with
    | nil =>
      intro p hp hk hu hw hb ha _
      exact Hc p.2 hk hu hw (hb.trans (hp.2.trans hBBc)) ha
    | cons a w ih =>
      intro p hp hk hu hw hb ha hmem
      have hin : p ∈ eraInputSelection σ Be a.natPred :=
        ⟨⟨hp.1, hp.2.trans hBBe⟩, hmem.1.1.2⟩
      obtain ⟨hr, hU, hW, hsum, _, havoid⟩ := He a.natPred p hin
      have hpower : p.1 ^ (4 / 3 : ℝ) ≤ p.1 :=
        Real.rpow_le_self_of_le_one hp.1.le (hp.2.trans hBone.le) (by norm_num)
      exact ih (eraBudgetReturn η J a.natPred p)
        ⟨Real.rpow_pos_of_pos hp.1 _, hpower.trans hp.2⟩
        (by change 2 - γ / 2 ≤ eraNextState η J a.natPred p.2 0; linarith only [hr, hγ])
        hU hW hsum (havoid ε ha) hmem.2
  intro p hp hk hu hw hb ha w hmem
  exact Hhistory w p hp hk hu hw hb ha hmem
