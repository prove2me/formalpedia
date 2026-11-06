-- Prove2me | solution 1 for BianchiIX.exists_era_selected_inputs_inverse
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:43:59.059705+00:00
-- url     : https://prove2.me/submissions/02eb6f94-926b-4398-9324-a0be6358aa88

import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Theorems.Thm_BianchiIX_exists_era_interval_inverse
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



/-- Selection by the actual output phase agrees exactly with the open inverse-branch image. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bstar > (0 : ℝ), Bstar < 1 ∧ ∀ B ∈ Ioc 0 Bstar,
          ∀ Γ : EraCurve, Γ.Admissible B → ∀ m : ℕ, m < ⌊1 / B ^ σ⌋₊ → ∀ x : ℝ,
            (B, Γ.state (2 / x)) ∈ eraSelectedInputs η J σ Bstar m ↔
              x ∈ eraInverseBranch η J m (B ^ σ) Γ.U Γ.W '' Ioo (2 * B ^ σ) (1 - 2 * B ^ σ) := by
  obtain ⟨δ, hδ, hδmax, Hδ⟩ := exists_era_interval_inverse
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, _, C, hC, Hinv⟩ := Hδ η hη hηδ J hJ
  obtain ⟨Bs, hBs, hBsone, Hbudget⟩ :=
    exists_retained_era_parameter_budget hε (by linarith : 0 ≤ C) hσ hσone hσJ
  refine ⟨Bs, hBs, hBsone, ?_⟩
  intro B hB Γ hΓ m hm x
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := Hbudget B hB
  have hcap : (m : ℝ) + 1 ≤ 1 / B ^ σ :=
    (show (m : ℝ) + 1 ≤ (⌊1 / B ^ σ⌋₊ : ℝ) by exact_mod_cast (Nat.succ_le_of_lt hm)).trans
      (Nat.floor_le (by positivity))
  have Hgraph := fun r (hr : r ∈ Icc (2 * ((m : ℝ) + 1 + B ^ σ))
      (2 * ((m : ℝ) + 2 - B ^ σ))) => hΓ r (by nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m])
  obtain ⟨_, _, _, _, H⟩ := Hinv m (B ^ σ) B Γ.U Γ.W hβ (by linarith)
    (hscale m hcap) hsmall hmargin Hgraph
  let φ := graphPhase (eraBoundedPhase η J m) Γ.U Γ.W
  let g := intervalRadiusInverse φ (2 * ((m : ℝ) + 1 + B ^ σ)) (2 * ((m : ℝ) + 2 - B ^ σ))
  constructor
  · intro hx
    let y := 2 / eraOutputRadius η J m (Γ.state (2 / x))
    have hy : y ∈ Ioo (2 * B ^ σ) (1 - 2 * B ^ σ) := hx.2
    obtain ⟨_, _, huniq, _⟩ := H y ⟨hy.1.le, hy.2.le⟩
    have hr : 2 / x ∈ Icc (2 * ((m : ℝ) + 1 + B ^ σ)) (2 * ((m : ℝ) + 2 - B ^ σ)) :=
      hx.1.2.2.2.2.2
    have hg : g y = 2 / x := (huniq (2 / x) hr rfl).symm
    refine ⟨y, hy, ?_⟩
    change 2 / g y = x
    rw [hg]
    field_simp
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hg, hfg, _⟩ := H y ⟨hy.1.le, hy.2.le⟩
    have hrec : 2 / eraInverseBranch η J m (B ^ σ) Γ.U Γ.W y = g y := by
      change 2 / (2 / g y) = g y
      field_simp
    rw [hrec]
    have HΓ := Hgraph (g y) ⟨hg.1.le, hg.2.le⟩
    refine ⟨⟨hB, hm, HΓ.1, HΓ.2.1, HΓ.2.2.1, ⟨hg.1.le, hg.2.le⟩⟩, ?_⟩
    change φ (g y) ∈ Ioo (2 * B ^ σ) (1 - 2 * B ^ σ)
    change φ (g y) = y at hfg
    rw [hfg]
    exact hy
