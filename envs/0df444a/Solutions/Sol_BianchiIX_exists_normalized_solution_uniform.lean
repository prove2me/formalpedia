-- Prove2me | solution 1 for BianchiIX.exists_normalized_solution_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:31:57.446308+00:00
-- url     : https://prove2.me/submissions/a3b93b10-b734-49de-bc15-a93e4fcf2c16

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Theorems.Thm_BianchiIX_contDiff_normalizedField
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

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.normalizedField_lipschitz_closedBall (x : NormalizedState) (r : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L normalizedField (closedBall x r) :=
  (contDiff_normalizedField 1).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall x r) (isCompact_closedBall x r)

end
end

/-- A bounded set of initial states has a common positive existence time. -/
theorem solution (R : ℝ) (hR : 0 ≤ R) :
    ∃ ε > (0 : ℝ), ∀ x : NormalizedState, ‖x‖ ≤ R → ∀ t₀ : ℝ,
      ∃ α : ℝ → NormalizedState, α t₀ = x ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt α (normalizedField (α t)) t := by
  obtain ⟨K, hK⟩ := normalizedField_lipschitz_closedBall 0 (R + 1)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : NormalizedState) (R + 1)).exists_bound_of_continuousOn
    (contDiff_normalizedField 1).continuous.continuousOn
  let L : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  let a : ℝ≥0 := ⟨R + 1, by positivity⟩
  let r : ℝ≥0 := ⟨R, hR⟩
  let ε : ℝ := 1 / (L + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hε, fun x hx t₀ => ?_⟩
  have hPL : IsPicardLindelof (fun _ => normalizedField)
      (tmin := t₀ - ε) (tmax := t₀ + ε) ⟨t₀, by constructor <;> linarith⟩ 0 a r L K := by
    apply IsPicardLindelof.of_time_independent (a := a) (r := r) (L := L) (K := K)
      (fun y hy => (hB y hy).trans (le_max_left B 0)) hK
    have htime : max (t₀ + ε - t₀) (t₀ - (t₀ - ε)) = ε := by simp
    rw [htime]
    change (L : ℝ) * ε ≤ (R + 1) - R
    dsimp [ε]
    have hden : 0 < (L : ℝ) + 1 := by positivity
    rw [mul_one_div, div_le_iff₀ hden]
    nlinarith
  obtain ⟨α, hinit, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt
    (x := x) (by
      rw [mem_closedBall, dist_zero_right]
      change ‖x‖ ≤ R
      exact hx)
  exact ⟨α, hinit, fun t ht =>
    (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)⟩
