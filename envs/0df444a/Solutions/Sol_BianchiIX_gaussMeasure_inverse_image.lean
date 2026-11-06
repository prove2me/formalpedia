-- Prove2me | solution 1 for BianchiIX.gaussMeasure_inverse_image
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:37:39.957598+00:00
-- url     : https://prove2.me/submissions/d80b1ee0-b4c4-4a75-832f-b2ed83a00e6e

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
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
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

end
end

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_gaussInv {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) :
    HasDerivAt (gaussInv a) (-1 / (a + x) ^ 2) x := by
  have hden : a + x ≠ 0 := ne_of_gt (by linarith)
  unfold gaussInv
  simpa only [one_div, id_eq] using ((hasDerivAt_id x).const_add a).fun_inv hden

end
end

section
open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

private theorem BianchiIX.measurableEmbedding_gaussInv (a : ℝ) : MeasurableEmbedding (gaussInv a) := by
  have h : MeasurableEmbedding (fun x : ℝ => (a + x)⁻¹) :=
    (MeasurableEquiv.inv ℝ).measurableEmbedding.comp
      (MeasurableEquiv.addLeft a).measurableEmbedding
  change MeasurableEmbedding (fun x : ℝ => 1 / (a + x))
  simpa only [one_div] using h

end
end

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

theorem solution {a : ℝ} (ha : 1 ≤ a) {A : Set ℝ}
    (hA : MeasurableSet A) (hsub : A ⊆ Ioo (0 : ℝ) 1) :
    gaussMeasure (gaussInv a '' A) = ∫⁻ x in A,
      ENNReal.ofReal (gaussWeight (gaussInv a x) * |deriv (gaussInv a) x|) := by
  have himg : gaussInv a '' A ⊆ Ioo (0 : ℝ) 1 := by
    rintro _ ⟨x, hx, rfl⟩
    have ht := hsub hx
    refine ⟨gaussInv_pos ha ht.1.le, ?_⟩
    exact (div_lt_one (by linarith [ht.1] : 0 < a + x)).mpr (by linarith [ht.1])
  rw [gaussMeasure_apply ((measurableEmbedding_gaussInv a).measurableSet_image.mpr hA) himg]
  rw [lintegral_image_eq_lintegral_abs_deriv_mul hA
    (fun x hx => (hasDerivAt_gaussInv ha (hsub hx).1.le).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (measurableEmbedding_gaussInv a).injective.injOn]
  apply lintegral_congr
  intro x
  rw [mul_comm, ← ENNReal.ofReal_mul' (abs_nonneg _)]
