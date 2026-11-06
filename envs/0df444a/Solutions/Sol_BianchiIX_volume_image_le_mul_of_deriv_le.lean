-- Prove2me | solution 1 for BianchiIX.volume_image_le_mul_of_deriv_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:25:18.311451+00:00
-- url     : https://prove2.me/submissions/5a5142d2-370a-4dcd-a664-9a51b865d196

import Theorems.Thm_BianchiIX_volume_image_eq_lintegral_abs_deriv
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


theorem solution {F F' G G' : ℝ → ℝ} {A : Set ℝ} {C : ℝ}
    (hA : MeasurableSet A) (hF : ∀ x ∈ A, HasDerivAt F (F' x) x)
    (hG : ∀ x ∈ A, HasDerivAt G (G' x) x) (hFinj : InjOn F A) (hGinj : InjOn G A)
    (hC : 0 ≤ C) (hbound : ∀ x ∈ A, |F' x| ≤ C * |G' x|) :
    volume (F '' A) ≤ ENNReal.ofReal C * volume (G '' A) := by
  rw [volume_image_eq_lintegral_abs_deriv hA hF hFinj,
    volume_image_eq_lintegral_abs_deriv hA hG hGinj]
  calc
    (∫⁻ x in A, ENNReal.ofReal |F' x|) ≤
        ∫⁻ x in A, ENNReal.ofReal C * ENNReal.ofReal |G' x| := by
      apply lintegral_mono_ae
      apply ae_restrict_of_forall_mem hA
      intro x hx
      rw [← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (hbound x hx)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
