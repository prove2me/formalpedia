-- Prove2me | solution 1 for BianchiIX.normalized_forward_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:40:08.785224+00:00
-- url     : https://prove2.me/submissions/3c35eaf3-2c39-48de-9a77-8cc31fc70041

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Theorems.Thm_BianchiIX_normalizedState_norm_bound
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_positive_walls_invariant
import Theorems.Thm_BianchiIX_normalized_wall_growth
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


theorem solution {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t M : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (htt : t₀ ≤ t)
    (hpos : positiveWalls (α t₀)) (hcon : stateConstraint (α t₀) = 1)
    (hwall : ∀ i : Fin 3, wallValue i (α t₀) ≤ M) :
    ‖α t‖ ≤ 1 + 3 * M * Real.exp (t - t₀) := by
  have hposall := normalized_positive_walls_invariant hI hopen hα ht₀ ht hpos
  have hp (i : Fin 3) : 0 ≤ wallValue i (α t₀) := by
    fin_cases i
    · exact hpos.1.le
    · exact hpos.2.1.le
    · exact hpos.2.2.le
  have H := normalizedState_norm_bound hposall
    ((normalized_constraint_constant hI hα ht₀ ht).trans hcon)
    (fun i => (normalized_wall_growth hI hopen hα ht₀ ht htt i (hp i)).trans
      (mul_le_mul_of_nonneg_right (hwall i) (Real.exp_pos _).le))
  simpa only [mul_assoc] using H
