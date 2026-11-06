-- Prove2me | solution 1 for BianchiIX.normalized_solution_unique
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:36:10.731383+00:00
-- url     : https://prove2.me/submissions/f8eacf5e-e6f6-4779-b61b-8065dd34454e

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Theorems.Thm_BianchiIX_normalized_solution_unique_Icc
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


theorem solution {I : Set ℝ} (hI : Convex ℝ I)
    {α β : ℝ → NormalizedState} {t₀ : ℝ}
    (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    (hβ : ∀ t ∈ I, HasDerivAt β (normalizedField (β t)) t)
    (ht₀ : t₀ ∈ I) (heq : α t₀ = β t₀) : EqOn α β I := by
  intro t ht
  have hsub : uIcc t₀ t ⊆ I := hI.ordConnected.uIcc_subset ht₀ ht
  exact normalized_solution_unique_Icc (fun u hu => hα u (hsub hu))
    (fun u hu => hβ u (hsub hu)) left_mem_uIcc heq right_mem_uIcc
