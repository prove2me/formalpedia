-- Prove2me | solution 1 for BianchiIX.measurePreserving_gaussMap
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:47:08.749684+00:00
-- url     : https://prove2.me/submissions/1a9656da-2002-42d0-b408-a65468e714ea

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Theorems.Thm_BianchiIX_ae_gaussMeasure_mem_unit
import Theorems.Thm_BianchiIX_gaussMap_preimage_ae
import Theorems.Thm_BianchiIX_gaussMeasure_inverse_sum
import Theorems.Thm_BianchiIX_gauss_inverse_images_disjoint
import Theorems.Thm_BianchiIX_measurable_gaussMap
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
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving

open Set MeasureTheory
open scoped ENNReal
open BianchiIX

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

theorem solution : MeasurePreserving gaussMap gaussMeasure gaussMeasure := by
  refine ⟨measurable_gaussMap, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_gaussMap hA,
    measure_congr (gaussMap_preimage_ae A),
    measure_iUnion (gauss_inverse_images_disjoint inter_subset_right)
      (fun j => (measurableEmbedding_gaussInv _).measurableSet_image.mpr
        (hA.inter measurableSet_Ioo)),
    gaussMeasure_inverse_sum (hA.inter measurableSet_Ioo) inter_subset_right]
  apply measure_congr
  filter_upwards [ae_gaussMeasure_mem_unit] with x hx
  change (x ∈ A ∩ Ioo (0 : ℝ) 1) = (x ∈ A)
  exact propext (and_iff_left hx)
