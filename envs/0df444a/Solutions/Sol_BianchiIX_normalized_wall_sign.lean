-- Prove2me | solution 1 for BianchiIX.normalized_wall_sign
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:57:02.634818+00:00
-- url     : https://prove2.me/submissions/46f791dd-3143-4096-9ea7-c436d6dbe4a2

import Definitions.Def_BianchiIX_Dynamics_Normalized
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
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- The exponential wall formula preserves both zero walls and their signs. -/
theorem solution {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (i : Fin 3) :
    (wallValue i (α t) = 0 ↔ wallValue i (α s) = 0) ∧
      (0 ≤ wallValue i (α t) ↔ 0 ≤ wallValue i (α s)) := by
  rw [normalized_wall_formula hI ho hα hs ht i]
  exact ⟨mul_eq_zero.trans (or_iff_left (Real.exp_ne_zero _)),
    mul_nonneg_iff_of_pos_right (Real.exp_pos _)⟩
