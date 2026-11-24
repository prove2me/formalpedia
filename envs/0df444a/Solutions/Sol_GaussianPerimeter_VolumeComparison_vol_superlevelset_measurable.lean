-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.vol_superlevelset_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:14:05.293321+00:00
-- url     : https://prove2.me/submissions/b8c7b759-45e9-486e-90cd-462cedd28cd0

module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Definitions.Def_GaussianPerimeter_PrekopaHelpers
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Definitions.Def_GaussianPerimeter_PrekopaLeindler

set_option autoImplicit true
@[expose] public section
public section
open GaussianPerimeter GaussianPerimeter.VolumeComparison
open MeasureTheory Set
open scoped Pointwise
namespace GaussianPerimeter.VolumeComparison
theorem _root_.solution (f : ℝ → ENNReal)
    : Measurable (fun t : ℝ ↦ volume {x | ENNReal.ofReal t ≤ f x}) := by
  apply Antitone.measurable
  intro a b hab
  apply measure_mono
  simp only [ofPred_subset_ofPred]
  intro z hz
  calc
    ENNReal.ofReal a ≤ ENNReal.ofReal b := ENNReal.ofReal_le_ofReal hab
    _ ≤ f z := hz
end GaussianPerimeter.VolumeComparison
