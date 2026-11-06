-- Prove2me | solution 1 for BianchiIX.volume_image_eq_lintegral_abs_deriv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:21:19.035952+00:00
-- url     : https://prove2.me/submissions/259e4cc6-6391-4dfd-880b-6f56dd66f907

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

namespace BianchiIX
end BianchiIX

open BianchiIX
noncomputable section
open Set Finset MeasureTheory
open scoped ENNReal


theorem solution {F F' : ℝ → ℝ} {A : Set ℝ}
    (hA : MeasurableSet A) (hF : ∀ x ∈ A, HasDerivAt F (F' x) x) (hinj : InjOn F A) :
    volume (F '' A) = ∫⁻ x in A, ENNReal.ofReal |F' x| := by
  simpa using lintegral_image_eq_lintegral_abs_deriv_mul hA
    (fun x hx => (hF x hx).hasDerivWithinAt) hinj (fun _ => 1)
