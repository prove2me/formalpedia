-- Prove2me | solution 1 for BianchiIX.normalized_wall_abs_growth
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:57:31.777581+00:00
-- url     : https://prove2.me/submissions/93754c00-13ce-4ef9-bee8-42b36681e81e

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Theorems.Thm_BianchiIX_normalized_wall_formula
import Theorems.Thm_BianchiIX_wall_rates_le_one
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

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.continuous_wallRate (i : Fin 3) : Continuous (wallRate i) := by
  change Continuous (fun x => wallRate i x)
  fin_cases i <;> dsimp [wallRate, rateOne, rateTwo, rateThree, shearSq] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.wallRate_le_one (i : Fin 3) (x : NormalizedState) : wallRate i x ≤ 1 := by
  have H := wall_rates_le_one (x 0) (x 1)
  fin_cases i
  · exact H.1
  · exact H.2.1
  · exact H.2.2

end
end

theorem solution {I : Set ℝ} (hI : Convex ℝ I) (ho : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) (i : Fin 3) :
    |wallValue i (α t)| ≤ |wallValue i (α s)| * Real.exp (t - s) := by
  have hc := (continuous_wallRate i).comp_continuousOn (HasDerivAt.continuousOn hα)
  have hi : IntervalIntegrable (fun u => wallRate i (α u)) volume s t :=
    (hc.mono (hI.ordConnected.uIcc_subset hs ht)).intervalIntegrable
  have H : (∫ u in s..t, wallRate i (α u)) ≤ t - s := by
    have H := intervalIntegral.integral_mono_on hst hi (intervalIntegrable_const (c := (1 : ℝ)))
      (fun u _ => wallRate_le_one i (α u))
    simpa using H
  rw [normalized_wall_formula hI ho hα hs ht i, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr H) (abs_nonneg _)
