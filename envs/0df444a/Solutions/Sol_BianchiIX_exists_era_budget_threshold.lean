-- Prove2me | solution 1 for BianchiIX.exists_era_budget_threshold
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T20:07:47.826349+00:00
-- url     : https://prove2.me/submissions/abe56ffe-87fd-4b54-985d-e72551aceb5b

import Definitions.Def_BianchiIX_Statistics_EraBudget
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Data.List.Induction
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology ENNReal


theorem solution {η Cv Ci C : ℝ} (hη : 0 < η)
    (hCv : 0 ≤ Cv) (hCi : 0 ≤ Ci) (hC : 0 ≤ C) :
    ∃ Bmax : ℝ, 0 < Bmax ∧ Bmax < 1 ∧ ∀ B ∈ Ioc 0 Bmax,
      B ^ η < 1 / 160 ∧
        2 * Ci * Real.sqrt B + 4 * Cv * B ^ (4 / 3 : ℝ) ≤ Real.log 2 ∧
        (25 / 16 : ℝ) * C * B ^ (17 / 30 : ℝ) ≤ 1 := by
  let c : Fin 4 → ℝ := ![1, 2 * Ci, 4 * Cv, (25 / 16) * C]
  let p : Fin 4 → ℝ := ![η, 1 / 2, 4 / 3, 17 / 30]
  let ε : Fin 4 → ℝ := ![1 / 160, Real.log 2 / 2, Real.log 2 / 2, 1]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Bmax, hpos, hupper, hbudget⟩ :=
    exists_common_rpow_budget (Finset.univ : Finset (Fin 4)) (C := c) (p := p) (ε := ε)
      (by intro i _; fin_cases i <;> dsimp [c] <;> positivity)
      (by intro i _; fin_cases i <;> dsimp [p] <;> positivity)
      (by intro i _; fin_cases i <;> dsimp [ε] <;> positivity)
      (by norm_num : (0 : ℝ) < 1)
  refine ⟨Bmax, hpos, hupper, fun B hB => ?_⟩
  have h₀ := hbudget B hB 0 (Finset.mem_univ _)
  have h₁ := hbudget B hB 1 (Finset.mem_univ _)
  have h₂ := hbudget B hB 2 (Finset.mem_univ _)
  have h₃ := hbudget B hB 3 (Finset.mem_univ _)
  change 1 * B ^ η < 1 / 160 at h₀
  change 2 * Ci * B ^ (1 / 2 : ℝ) < Real.log 2 / 2 at h₁
  change 4 * Cv * B ^ (4 / 3 : ℝ) < Real.log 2 / 2 at h₂
  change (25 / 16 : ℝ) * C * B ^ (17 / 30 : ℝ) < 1 at h₃
  rw [← Real.sqrt_eq_rpow] at h₁
  exact ⟨by simpa only [one_mul] using h₀, by linarith, h₃.le⟩
