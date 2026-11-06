-- Prove2me | solution 1 for BianchiIX.gaussMeasure_inverse_sum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:45:49.059344+00:00
-- url     : https://prove2.me/submissions/43ee4132-a374-4e8a-802e-d02ad7de9158

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Theorems.Thm_BianchiIX_gaussMeasure_inverse_image
import Theorems.Thm_BianchiIX_gaussWeight_inverse_jacobian
import Theorems.Thm_BianchiIX_gaussWeight_transfer_tsum
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
import Mathlib.MeasureTheory.Measure.WithDensity

open Set Filter MeasureTheory
open scoped Topology ENNReal
open BianchiIX

section
open Set MeasureTheory
open scoped ENNReal
open BianchiIX
noncomputable section

private theorem BianchiIX.gaussMeasure_apply {A : Set ℝ} (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    gaussMeasure A = ∫⁻ x in A, ENNReal.ofReal (gaussWeight x) := by
  rw [gaussMeasure, withDensity_apply _ hA, Measure.restrict_restrict_of_subset hsub]

end
end

theorem solution {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    (∑' j : ℕ, gaussMeasure (gaussInv ((j : ℝ) + 1) '' A)) = gaussMeasure A := by
  have heq (j : ℕ) := gaussMeasure_inverse_image
    (a := (j : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) j]) hA hsub
  simp_rw [heq]
  rw [← lintegral_tsum, gaussMeasure_apply hA hsub]
  · apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem hA
    exact fun x hx => gaussWeight_transfer_tsum (hsub hx).1.le
  · intro j
    have hm : Measurable (fun x : ℝ => ENNReal.ofReal
        ((1 / Real.log 2) * (1 / ((j : ℝ) + 1 + x) - 1 / ((j : ℝ) + 1 + 1 + x)))) :=
      (measurable_const.mul
        ((measurable_const.div (measurable_const.add measurable_id)).sub
          (measurable_const.div (measurable_const.add measurable_id)))).ennreal_ofReal
    apply hm.aemeasurable.congr
    apply ae_restrict_of_forall_mem hA
    intro x hx
    dsimp only
    rw [gaussWeight_inverse_jacobian (by linarith [Nat.cast_nonneg (α := ℝ) j]) (hsub hx).1.le]
