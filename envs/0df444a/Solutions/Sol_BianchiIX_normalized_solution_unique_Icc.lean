-- Prove2me | solution 1 for BianchiIX.normalized_solution_unique_Icc
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:30:33.639588+00:00
-- url     : https://prove2.me/submissions/169123c4-d92d-41a0-928b-b509157350dc

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

private theorem BianchiIX.normalizedField_lipschitz_closedBall (x : NormalizedState) (r : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L normalizedField (closedBall x r) :=
  (contDiff_normalizedField 1).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall x r) (isCompact_closedBall x r)

theorem solution {α β : ℝ → NormalizedState} {a b t₀ : ℝ}
    (hα : ∀ t ∈ Icc a b, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ Icc a b, HasDerivAt β (normalizedField (β t)) t)
    (ht₀ : t₀ ∈ Icc a b) (heq : α t₀ = β t₀) : EqOn α β (Icc a b) := by
  have hcα := HasDerivAt.continuousOn hα
  have hcβ := HasDerivAt.continuousOn hβ
  obtain ⟨A, hA⟩ := isCompact_Icc.exists_bound_of_continuousOn hcα
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcβ
  obtain ⟨L, hL⟩ := normalizedField_lipschitz_closedBall 0 (max A B)
  have hαball (t : ℝ) (ht : t ∈ Icc a b) : α t ∈ closedBall 0 (max A B) := by
    simpa only [mem_closedBall, dist_zero_right] using (hA t ht).trans (le_max_left A B)
  have hβball (t : ℝ) (ht : t ∈ Icc a b) : β t ∈ closedBall 0 (max A B) := by
    simpa only [mem_closedBall, dist_zero_right] using (hB t ht).trans (le_max_right A B)
  have hleft : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc_right ht₀.2
  have hright : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
  rw [← Icc_union_Icc_eq_Icc ht₀.1 ht₀.2]
  apply EqOn.union
  · exact ODE_solution_unique_of_mem_Icc_left
      (v := fun _ => normalizedField) (s := fun _ => closedBall 0 (max A B))
      (fun _ _ => hL) (hcα.mono hleft)
      (fun t ht => (hα t (hleft (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hαball t (hleft (Ioc_subset_Icc_self ht))) (hcβ.mono hleft)
      (fun t ht => (hβ t (hleft (Ioc_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hβball t (hleft (Ioc_subset_Icc_self ht))) heq
  · exact ODE_solution_unique_of_mem_Icc_right
      (v := fun _ => normalizedField) (s := fun _ => closedBall 0 (max A B))
      (fun _ _ => hL) (hcα.mono hright)
      (fun t ht => (hα t (hright (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hαball t (hright (Ico_subset_Icc_self ht))) (hcβ.mono hright)
      (fun t ht => (hβ t (hright (Ico_subset_Icc_self ht))).hasDerivWithinAt)
      (fun t ht => hβball t (hright (Ico_subset_Icc_self ht))) heq
