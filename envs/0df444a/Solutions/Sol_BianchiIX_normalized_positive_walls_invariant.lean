-- Prove2me | solution 1 for BianchiIX.normalized_positive_walls_invariant
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:33:22.779401+00:00
-- url     : https://prove2.me/submissions/cf12971f-0fa5-4c5b-8c52-337af9b545c0

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Theorems.Thm_BianchiIX_normalized_wall_formula
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

noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.normalized_wall_pos {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (i : Fin 3) (hpos : 0 < wallValue i (α t₀)) :
    0 < wallValue i (α t) := by
  rw [normalized_wall_formula hI hopen hα ht₀ ht i]
  exact mul_pos hpos (Real.exp_pos _)

theorem solution {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (hpos : positiveWalls (α t₀)) :
    positiveWalls (α t) :=
  ⟨normalized_wall_pos hI hopen hα ht₀ ht 0 hpos.1,
    normalized_wall_pos hI hopen hα ht₀ ht 1 hpos.2.1,
    normalized_wall_pos hI hopen hα ht₀ ht 2 hpos.2.2⟩
