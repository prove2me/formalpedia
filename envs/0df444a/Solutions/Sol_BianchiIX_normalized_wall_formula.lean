-- Prove2me | solution 1 for BianchiIX.normalized_wall_formula
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:27:43.385262+00:00
-- url     : https://prove2.me/submissions/f73cd6a6-420a-4a8e-b928-44eb997970db

import Definitions.Def_BianchiIX_Dynamics_WallEvolution
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

private theorem BianchiIX.homogeneous_solution_eq_exp_integral {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {f a : ℝ → ℝ} (ha : ContinuousOn a I)
    (hf : ∀ t ∈ I, HasDerivAt f (a t * f t) t) {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) :
    f t = f t₀ * Real.exp (∫ u in t₀..t, a u) := by
  let P : ℝ → ℝ := fun v => ∫ u in t₀..v, a u
  have hP (v : ℝ) (hv : v ∈ I) : HasDerivAt P (a v) v :=
    intervalIntegral.integral_hasDerivAt_right
      (ha.mono (hI.ordConnected.uIcc_subset ht₀ hv)).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter hopen ha v hv)
      (ha.continuousAt (hopen.mem_nhds hv))
  have hF (v : ℝ) (hv : v ∈ I) :
      HasDerivAt (fun u => f u * Real.exp (-P u)) 0 v := by
    convert! (hf v hv).mul (hP v hv).neg.exp using 1
    ring
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hF v hv).hasDerivWithinAt) (C := 0) (fun _ _ => by simp) ht₀ ht
  have heq : f t * Real.exp (-P t) = f t₀ := by
    simpa [P, sub_eq_zero] using H
  calc
    f t = (f t * Real.exp (-P t)) * Real.exp (P t) := by
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ = f t₀ * Real.exp (P t) := by rw [heq]

private theorem BianchiIX.continuous_wallRate (i : Fin 3) : Continuous (wallRate i) := by
  change Continuous (fun x => wallRate i x)
  fin_cases i <;> dsimp [wallRate, rateOne, rateTwo, rateThree, shearSq] <;> fun_prop

private theorem BianchiIX.hasDerivAt_wallValue {α : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t) (i : Fin 3) :
    HasDerivAt (fun u => wallValue i (α u)) (wallRate i (α t) * wallValue i (α t)) t := by
  have H := hasDerivAt_pi.mp hα (i.addNat 2)
  fin_cases i <;> exact H

theorem solution {I : Set ℝ} (hI : Convex ℝ I) (hopen : IsOpen I)
    {α : ℝ → NormalizedState} (hα : ∀ t ∈ I, HasDerivAt α (normalizedField (α t)) t)
    {t₀ t : ℝ} (ht₀ : t₀ ∈ I) (ht : t ∈ I) (i : Fin 3) :
    wallValue i (α t) = wallValue i (α t₀) * Real.exp (∫ u in t₀..t, wallRate i (α u)) :=
  homogeneous_solution_eq_exp_integral hI hopen
    ((continuous_wallRate i).comp_continuousOn (HasDerivAt.continuousOn hα))
    (fun u hu => hasDerivAt_wallValue (hα u hu) i) ht₀ ht
