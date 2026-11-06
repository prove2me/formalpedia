-- Prove2me | solution 1 for BianchiIX.exists_era_curve_step
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:46:55.389214+00:00
-- url     : https://prove2.me/submissions/9bc3fea9-980e-4504-ab0a-be68f07dab0e

import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_era_amplitude_extension
import Theorems.Thm_BianchiIX_exists_era_retained_phase_loss
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

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal



/-- The actual inverse branches, successor curves, and stopping loss hold at one common amplitude scale. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ C ≥ (1 : ℝ), ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
          ∀ B ∈ Ioc 0 Bstar, ∀ Γ : EraCurve, Γ.Admissible B → Γ.StepEstimates η J σ B C := by
  obtain ⟨δl, hδl, hδlmax, HL⟩ := exists_era_retained_phase_loss
  obtain ⟨δe, hδe, _, HE⟩ := exists_era_amplitude_extension
  refine ⟨min δl δe, lt_min hδl hδe, (min_le_left _ _).trans hδlmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨C, hC, Bl, hBl, hBlone, Hloss⟩ :=
    HL η hη (hηδ.trans (min_le_left _ _)) J (by omega) σ hσ hσone hσJ
  obtain ⟨ε, hε, _, A, hA, Hextend⟩ := HE η hη (hηδ.trans (min_le_right _ _)) J hJ
  obtain ⟨Be, hBe, _, Hbudget⟩ := exists_retained_era_parameter_budget hε
    (by linarith : 0 ≤ A) hσ hσone hσJ
  refine ⟨C, hC, min Bl Be, lt_min hBl hBe, (min_le_left _ _).trans_lt hBlone, ?_⟩
  intro B hB Γ hΓ
  obtain ⟨hβ, hβmax, Hbranch, Hdisjoint, _, hvol⟩ :=
    Hloss B ⟨hB.1, hB.2.trans (min_le_left _ _)⟩ Γ.U Γ.W hΓ
  obtain ⟨_, _, hsmall, hmargin, hscale⟩ := Hbudget B ⟨hB.1, hB.2.trans (min_le_right _ _)⟩
  have Hext (m : ℕ) (hm : m < ⌊1 / B ^ σ⌋₊) := Hextend m (B ^ σ) B Γ.U Γ.W hβ
    (by linarith) (hscale m (by
      have Hcast : (m : ℝ) + 1 ≤ (⌊1 / B ^ σ⌋₊ : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hm)
      exact Hcast.trans (Nat.floor_le (by positivity)))) hsmall hmargin (by
        intro r hr
        apply hΓ r
        nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m])
  refine ⟨hβ, hβmax, ?_, ?_, ?_, Hdisjoint, hvol⟩
  · intro m hm
    exact ⟨(Hbranch m (Finset.mem_range.mpr hm)).1, (Hbranch m (Finset.mem_range.mpr hm)).2.2⟩
  · intro m hm r _
    obtain ⟨hθ, hcu, hcw, _, Hb⟩ := Hext m hm
    obtain ⟨hu, hw, hsum, hdu, hdw⟩ := Hb r
    exact ⟨hu, hw, hsum, hcu.contDiffAt, hcw.contDiffAt,
      hdu.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) (by linarith)),
      hdw.trans (mul_le_of_le_one_left (Real.sqrt_nonneg _) (by linarith))⟩
  · intro m hm y hy
    obtain ⟨_, _, _, Hmatch, _⟩ := Hext m hm
    obtain ⟨hk, hu, hw, _, _⟩ := Hmatch y hy
    let g := intervalRadiusInverse (graphPhase (eraBoundedPhase η J m) Γ.U Γ.W)
      (2 * ((m : ℝ) + 1 + B ^ σ)) (2 * ((m : ℝ) + 2 - B ^ σ))
    have hrec : g y = 2 / eraInverseBranch η J m (B ^ σ) Γ.U Γ.W y := by
      change g y = 2 / (2 / g y)
      field_simp
    change eraOutputRadius η J m (Γ.state (g y)) = 2 / y at hk
    change (Γ.successor η J m (B ^ σ)).U (2 / y) = eraOutputState η J m (Γ.state (g y)) 1 at hu
    change (Γ.successor η J m (B ^ σ)).W (2 / y) = eraOutputState η J m (Γ.state (g y)) 3 at hw
    rw [hrec] at hk hu hw
    exact ⟨hk, hu, hw⟩
