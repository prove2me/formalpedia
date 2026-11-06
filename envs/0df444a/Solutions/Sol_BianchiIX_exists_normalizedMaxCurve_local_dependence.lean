-- Prove2me | solution 1 for BianchiIX.exists_normalizedMaxCurve_local_dependence
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:18:13.537057+00:00
-- url     : https://prove2.me/submissions/b738ac44-8ecc-487b-b0d7-e62b6abfcc28

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
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


/-- The actual maximal solutions agree with one uniformly Lipschitz local family. -/
theorem solution (x₀ : NormalizedState) (t₀ : ℝ) :
    ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∃ L : ℝ≥0,
      (∀ x ∈ closedBall x₀ r, Ioo (t₀ - ε) (t₀ + ε) ⊆ normalizedMaxDomain x t₀) ∧
      ContinuousOn (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (closedBall x₀ r ×ˢ Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        LipschitzOnWith L (fun x => normalizedMaxCurve x t₀ t) (closedBall x₀ r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hPL⟩ :=
    IsPicardLindelof.of_contDiffAt_one ((contDiff_normalizedField 1).contDiffAt (x := x₀))
  obtain ⟨α, hα, L', hLip⟩ :=
    (hPL t₀).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := by constructor <;> linarith
  let S (x : NormalizedState) (hx : x ∈ closedBall x₀ r) : NormalizedSolution x t₀ :=
    ⟨Ioo (t₀ - ε) (t₀ + ε), isOpen_Ioo, convex_Ioo _ _, ht₀, α x, (hα x hx).1,
      fun t ht => ((hα x hx).2 t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)⟩
  have heq (x : NormalizedState) (hx : x ∈ closedBall x₀ r)
      (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      normalizedMaxCurve x t₀ t = α x t := normalizedMaxCurve_eqOn (S x hx) ht
  have hc : ContinuousOn (fun z : NormalizedState × ℝ => α z.1 z.2)
      (closedBall x₀ r ×ˢ Icc (t₀ - ε) (t₀ + ε)) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ L'
      (fun x hx => HasDerivWithinAt.continuousOn (hα x hx).2) hLip
  refine ⟨r, hr, ε, hε, L', fun x hx => (S x hx).domain_subset_maximal, ?_, ?_⟩
  · exact (hc.mono (prod_subset_prod_right Ioo_subset_Icc_self)).congr
      (fun z hz => heq z.1 hz.1 z.2 hz.2)
  · intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [heq x hx t ht, heq y hy t ht]
    exact (hLip t (Ioo_subset_Icc_self ht)).dist_le_mul x hx y hy
