-- Prove2me | solution 1 for BianchiIX.normalizedMaxDomain_contains_extension
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:42:35.425828+00:00
-- url     : https://prove2.me/submissions/24e330c6-e0a6-44b9-9826-1e190d8a33b0

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Theorems.Thm_BianchiIX_normalized_solution_glue
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
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.convex_union_real {I J : Set ℝ} (hI : Convex ℝ I) (hJ : Convex ℝ J)
    {s : ℝ} (hsI : s ∈ I) (hsJ : s ∈ J) : Convex ℝ (I ∪ J) := by
  rw [convex_iff_ordConnected]
  refine ⟨fun x hx y hy z hz => ?_⟩
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (hI.ordConnected.out hx hy hz)
  · by_cases hzs : z ≤ s
    · exact Or.inl (hI.ordConnected.out hx hsI ⟨hz.1, hzs⟩)
    · exact Or.inr (hJ.ordConnected.out hsJ hy ⟨le_of_not_ge hzs, hz.2⟩)
  · by_cases hzs : z ≤ s
    · exact Or.inr (hJ.ordConnected.out hx hsJ ⟨hz.1, hzs⟩)
    · exact Or.inl (hI.ordConnected.out hsI hy ⟨le_of_not_ge hzs, hz.2⟩)
  · exact Or.inr (hJ.ordConnected.out hx hy hz)

end
end

theorem solution {x₀ : NormalizedState} {t₀ s : ℝ}
    {J : Set ℝ} (hJ : Convex ℝ J) (hoJ : IsOpen J)
    {β : ℝ → NormalizedState}
    (hβ : ∀ t ∈ J, HasDerivAt β (normalizedField (β t)) t)
    (hs : s ∈ normalizedMaxDomain x₀ t₀) (hsJ : s ∈ J)
    (heq : normalizedMaxCurve x₀ t₀ s = β s) : J ⊆ normalizedMaxDomain x₀ t₀ := by
  let S := maximalNormalizedSolution x₀ t₀
  obtain ⟨γ, hγS, _, hγ⟩ := normalized_solution_glue
    S.convex_domain S.isOpen_domain hJ hoJ S.hasDerivAt hβ hs hsJ heq
  let T : NormalizedSolution x₀ t₀ :=
    ⟨S.domain ∪ J, S.isOpen_domain.union hoJ,
      convex_union_real S.convex_domain hJ hs hsJ, Or.inl S.initial_mem,
      γ, (hγS S.initial_mem).trans S.initial_eq, hγ⟩
  exact subset_union_right.trans T.domain_subset_maximal
