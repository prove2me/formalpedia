-- Prove2me | solution 1 for BianchiIX.image_sub_le_clock_sub_of_deriv_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:34:01.178987+00:00
-- url     : https://prove2.me/submissions/b4975d34-65fa-491d-a7f3-29ba0d08c37a

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
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
    {f f' z z' : ℝ → ℝ} {C s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hz : ∀ u ∈ I, HasDerivAt z (z' u) u)
    (hbound : ∀ u ∈ I, f' u ≤ C * z' u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t - f s ≤ C * (z t - z s) := by
  have hd (u : ℝ) (hh : u ∈ I) := (hf u hh).sub ((hz u hh).const_mul C)
  have hanti := antitoneOn_of_deriv_nonpos hI (HasDerivAt.continuousOn hd)
    (fun u hh => (hd u (interior_subset hh)).differentiableAt.differentiableWithinAt)
    (fun u hh => by rw [(hd u (interior_subset hh)).deriv]; linarith [hbound u (interior_subset hh)])
  have H := hanti hs ht hst
  dsimp at H
  linarith
