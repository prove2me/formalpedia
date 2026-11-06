-- Prove2me | solution 1 for BianchiIX.le_exp_of_clock_deriv_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:01:41.932032+00:00
-- url     : https://prove2.me/submissions/e67d1587-066d-41ee-80b3-671d2845a4e0

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set


theorem solution {I : Set ℝ} (hI : Convex ℝ I)
    {f f' z z' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hz : ∀ u ∈ I, HasDerivAt z (z' u) u)
    (hbound : ∀ u ∈ I, f' u ≤ c * z' u * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (z t - z s)) := by
  let g : ℝ → ℝ := fun u => f u * Real.exp (-c * z u)
  have hg (u : ℝ) (hu : u ∈ I) :
      HasDerivAt g ((f' u - c * z' u * f u) * Real.exp (-c * z u)) u := by
    convert! (hf u hu).mul ((hz u hu).const_mul (-c)).exp using 1
    ring
  have hmono : AntitoneOn g I := antitoneOn_of_deriv_nonpos hI
    (fun u hu => (hg u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hg u (interior_subset hu)).differentiableAt.differentiableWithinAt)
    (fun u hu => by
      rw [(hg u (interior_subset hu)).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hbound u (interior_subset hu))) (Real.exp_pos _).le)
  calc
    f t = g t * Real.exp (c * z t) := by
      dsimp [g]
      rw [mul_assoc, ← Real.exp_add]
      simp
    _ ≤ g s * Real.exp (c * z t) := mul_le_mul_of_nonneg_right (hmono hs ht hst) (Real.exp_pos _).le
    _ = f s * Real.exp (c * (z t - z s)) := by
      dsimp [g]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
