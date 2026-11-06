-- Prove2me | solution 1 for BianchiIX.exists_era_retained_phase_loss
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:45:37.397321+00:00
-- url     : https://prove2.me/submissions/32351632-b4e7-42e0-827d-d7efafba9494

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_era_inverse_branch_estimates
import Theorems.Thm_BianchiIX_exists_retained_era_parameter_budget
import Theorems.Thm_BianchiIX_finite_gauss_branch_loss
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

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal



/-- All retained actual digits share one threshold; their open intervals lose at most ten phase margins. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 4 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ C ≥ (1 : ℝ), ∃ Bstar > (0 : ℝ), Bstar < 1 ∧
        ∀ B ∈ Ioc 0 Bstar, ∀ U W : ℝ → ℝ,
          (∀ r : ℝ, 2 < r → 0 < U r ∧ 0 < W r ∧ U r + W r ≤ B ∧
            ContDiffAt ℝ 1 U r ∧ ContDiffAt ℝ 1 W r ∧
            |deriv U r| ≤ Real.sqrt (U r) ∧ |deriv W r| ≤ Real.sqrt (W r)) →
          let β := B ^ σ
          let N := ⌊1 / β⌋₊
          let K := Icc (2 * β) (1 - 2 * β)
          let h := fun m => eraInverseBranch η J m β U W
          0 < β ∧ β < 1 / 160 ∧
          (∀ m ∈ Finset.range N, StrictAntiOn (h m) K ∧
            h m '' K = Icc (h m (1 - 2 * β)) (h m (2 * β)) ∧
            ∀ y ∈ K, h m y ∈ Ioo (1 / ((m : ℝ) + 2)) (1 / ((m : ℝ) + 1)) ∧
              graphPhase (eraBoundedPhase η J m) U W (2 / h m y) = y ∧
              ContDiffAt ℝ 1 (h m) y ∧ deriv (h m) y < 0 ∧
              |h m y - gaussInv ((m : ℝ) + 1) y| ≤ C * B / ((m : ℝ) + 1) ^ 2 ∧
              |Real.log (|deriv (h m) y| / |deriv (gaussInv ((m : ℝ) + 1)) y|)| ≤
                5 * C * Real.sqrt B) ∧
          (↑(Finset.range N) : Set ℕ).PairwiseDisjoint
            (fun m => Ioo (h m (1 - 2 * β)) (h m (2 * β))) ∧
          MeasurableSet (Ioo (0 : ℝ) 1 \ eraRetainedPhases η J N β U W) ∧
          volume (Ioo (0 : ℝ) 1 \ eraRetainedPhases η J N β U W) ≤ ENNReal.ofReal (10 * β) := by
  obtain ⟨δ, hδ, hδmax, H⟩ := exists_era_inverse_branch_estimates
  refine ⟨δ, hδ, hδmax, ?_⟩
  intro η hη hηδ J hJ σ hσ hσone hσJ
  obtain ⟨ε, hε, _, C, hC, HE⟩ := H η hη hηδ J hJ
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨Bstar, hBs, hBsone, HB⟩ := exists_retained_era_parameter_budget hε hC0 hσ hσone hσJ
  refine ⟨C, hC, Bstar, hBs, hBsone, ?_⟩
  intro B hB U W Hgraph β N K h
  obtain ⟨hβ, hβmax, hsmall, hmargin, hscale⟩ := HB B hB
  change 0 < β at hβ
  change β < 1 / 160 at hβmax
  change B ≤ ε * (β / 2) ^ (2 * J) at hsmall
  change C * B < β / 4 at hmargin
  have hJends : 2 * β < 1 - 2 * β := by linarith
  have hleft : 2 * β ∈ K := ⟨le_rfl, hJends.le⟩
  have hright : 1 - 2 * β ∈ K := ⟨hJends.le, le_rfl⟩
  have hcap (m : ℕ) (hm : m ∈ Finset.range N) : (m : ℝ) + 1 ≤ 1 / β := by
    have hnat : m + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hm)
    have hcast : (m : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hnat
    exact hcast.trans (Nat.floor_le (by positivity))
  have Hbranch (m : ℕ) (hm : m ∈ Finset.range N) :=
    HE m β B U W hβ (by linarith) (hscale m (hcap m hm)) hsmall hmargin (by
      intro r hr
      apply Hgraph r
      nlinarith [hr.1, Nat.cast_nonneg (α := ℝ) m])
  have Hloss := finite_gauss_branch_loss (N := N) hβ.le (by linarith) (mul_nonneg hC0 hB.1.le)
    (L := fun m => h m (2 * β)) (R := fun m => h m (1 - 2 * β))
    (fun m hm => (Hbranch m hm).1 hleft hright hJends)
    (fun m hm => ((Hbranch m hm).2 _ hright).1.1)
    (fun m hm => ((Hbranch m hm).2 _ hleft).1.2)
    (fun m hm => ((Hbranch m hm).2 _ hleft).2.2.2.2.1)
    (fun m hm => ((Hbranch m hm).2 _ hright).2.2.2.2.1)
  have htail : 1 / ((N : ℝ) + 1) < β := by
    have Hfloor := Nat.lt_floor_add_one (1 / β)
    have Hmul := (div_lt_iff₀ hβ).mp Hfloor
    exact (div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr (by nlinarith)
  refine ⟨hβ, hβmax, ?_, Hloss.1, Hloss.2.1, Hloss.2.2.trans ?_⟩
  · intro m hm
    have hcont : ContinuousOn (h m) K :=
      fun y hy => ((Hbranch m hm).2 y hy).2.2.1.continuousAt.continuousWithinAt
    exact ⟨(Hbranch m hm).1,
      hcont.image_Icc_of_antitoneOn hJends.le (Hbranch m hm).1.antitoneOn, (Hbranch m hm).2⟩
  · apply ENNReal.ofReal_le_ofReal
    nlinarith
