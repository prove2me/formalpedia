-- Prove2me | solution 1 for BianchiIX.exists_common_physical_era_sequence
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T05:24:05.840943+00:00
-- url     : https://prove2.me/submissions/db2475f2-e177-40a6-add2-cee2193dd3e7

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalEraData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Theorems.Thm_BianchiIX_EraSurvivor_physical_era_sequence
import Theorems.Thm_BianchiIX_exists_common_borel_era_orbit
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
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
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.ByContra
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Interval.Set.Monotone

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- Jointly Borel complete physical eras outside one invariant null set, with the full statistical law. -/
theorem solution
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
          geometricException ⊆ N ∧
          (∀ x : NormalizedState, ∀ s ∈ normalizedMaxDomain x 0,
            normalizedMaxCurve x 0 s ∈ N ↔ x ∈ N) ∧
          (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
            IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
            (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
            (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
            volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
          ∃ K : ↥(physicalPhaseSpace \ N) → ℕ → ℕ+, Measurable K ∧
          ∃ Y : ↥(physicalPhaseSpace \ N) → ℕ → CoreAngleState, Measurable Y ∧
          ∃ t : ↥(physicalPhaseSpace \ N) → ℕ → ℝ, Measurable t ∧
          ∃ a : ↥(physicalPhaseSpace \ N) → ℕ → Fin 6, Measurable a ∧
            ∀ x, PhysicalEraSequence η J x.val (K x) (Y x) (t x) (a x) := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_common_borel_era_orbit hBirkhoff hBrehm
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨Bcap, _, _, N, hNm, hNp, hNg, hNi, hNn, hNfour,
    W, _, p, _, had, _, has, _, hat, haf, Hp⟩ := H η hη hηδ J hJ σ hσ hσone hσJ
  refine ⟨N, hNm, hNp, hNg, hNi, hNn, hNfour,
    (fun x n => EraSurvivor.digits (p x) (n + 1)), ?_,
    (fun x n => EraSurvivor.state (p x) (n + 1)), ?_,
    (fun x n => EraSurvivor.physicalTime (W x.val) (p x) (n + 1)), ?_,
    (fun x n => EraSurvivor.physicalFrame (W x.val) (p x) (n + 1)), ?_, ?_⟩
  · exact measurable_pi_lambda _ (fun n => (measurable_pi_apply (n + 1)).comp had)
  · exact measurable_pi_lambda _ (fun n => (measurable_pi_apply (n + 1)).comp has)
  · exact measurable_pi_lambda _ (fun n => (measurable_pi_apply (n + 1)).comp hat)
  · exact measurable_pi_lambda _ (fun n => (measurable_pi_apply (n + 1)).comp haf)
  · intro x
    obtain ⟨_, Hstat, _, _, Hmono, Htop, Hn⟩ := Hp x
    exact EraSurvivor.physical_era_sequence (W x.val) (p x) x.property.1.2 Hstat
      (fun n => ⟨(Hn n).1, (Hn n).2.1⟩) Hmono Htop
      (fun n => ⟨(Hn n).2.2.1, (Hn n).2.2.2.2⟩)
