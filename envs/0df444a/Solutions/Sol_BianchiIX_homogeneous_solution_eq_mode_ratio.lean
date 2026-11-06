-- Prove2me | solution 1 for BianchiIX.homogeneous_solution_eq_mode_ratio
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:51:29.705988+00:00
-- url     : https://prove2.me/submissions/1124aa81-5904-47d2-86de-6dc4675a678f

import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set


/-- Division by a nonzero fundamental solution gives every scalar solution. -/
theorem solution {I : Set ℝ} (hI : Convex ℝ I)
    {f g a : ℝ → ℝ} (hf : ∀ t ∈ I, HasDerivAt f (a t * f t) t)
    (hg : ∀ t ∈ I, HasDerivAt g (a t * g t) t) (hzero : ∀ t ∈ I, g t ≠ 0)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) : f t = f s * (g t / g s) := by
  have hq (u : ℝ) (hu : u ∈ I) : HasDerivAt (fun v => f v / g v) 0 u := by
    convert! (hf u hu).div (hg u hu) (hzero u hu) using 1
    ring
  have H := hI.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (hq u hu).hasDerivWithinAt) (C := 0) (fun _ _ => by simp) hs ht
  have heq : f t / g t = f s / g s := by simpa [sub_eq_zero] using H
  rw [← mul_div_assoc]
  exact (eq_div_iff (hzero s hs)).mpr ((div_eq_div_iff (hzero t ht) (hzero s hs)).mp heq)
