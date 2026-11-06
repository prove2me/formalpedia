-- Prove2me | solution 1 for BianchiIX.normalized_wall_growth
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:34:33.444363+00:00
-- url     : https://prove2.me/submissions/5b3cdf68-19f1-4455-b137-330bdb442775

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

noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.continuous_wallRate (i : Fin 3) : Continuous (wallRate i) := by
  change Continuous (fun x => wallRate i x)
  fin_cases i <;> dsimp [wallRate, rateOne, rateTwo, rateThree, shearSq] <;> fun_prop

private theorem BianchiIX.wallRate_le_one (i : Fin 3) (x : NormalizedState) : wallRate i x ≤ 1 := by
  have H := wall_rates_le_one (x 0) (x 1)
  fin_cases i
  · exact H.1
  · exact H.2.1
  · exact H.2.2

theorem solution {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (htt : t₀ ≤ t)
    (i : Fin 3) (hpos : 0 ≤ wallValue i (α t₀)) :
    wallValue i (α t) ≤ wallValue i (α t₀) * Real.exp (t - t₀) := by
  have hc : ContinuousOn (fun u => wallRate i (α u)) I :=
    (continuous_wallRate i).comp_continuousOn (HasDerivAt.continuousOn hα)
  have hi : IntervalIntegrable (fun u => wallRate i (α u)) volume t₀ t :=
    (hc.mono (hI.ordConnected.uIcc_subset ht₀ ht)).intervalIntegrable
  have H : (∫ u in t₀..t, wallRate i (α u)) ≤ t - t₀ := by
    have H := intervalIntegral.integral_mono_on htt hi (intervalIntegrable_const (c := (1 : ℝ)))
      (fun u _ => wallRate_le_one i (α u))
    simpa using H
  rw [normalized_wall_formula hI hopen hα ht₀ ht i]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr H) hpos
