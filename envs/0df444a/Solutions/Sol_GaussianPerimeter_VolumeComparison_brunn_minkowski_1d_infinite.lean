-- Prove2me | solution 1 for GaussianPerimeter.VolumeComparison.brunn_minkowski_1d_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:20:06.654547+00:00
-- url     : https://prove2.me/submissions/61c8a107-41ec-490c-95e4-4eed44e4addb

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
theorem _root_.solution
    {A B C : Set ℝ} (ha : volume A = ⊤) (hb : B.Nonempty) (hc : A + B ⊆ C) :
    volume A + volume B ≤ volume C := calc
  volume A + volume B = volume (A + {hb.some}) := by simp [ha]  -- since both sides = ⊤
  _ ≤ volume (A + B) := measure_mono (add_subset_add_left (singleton_subset_iff.mpr hb.some_mem))
  _ ≤ volume C := measure_mono hc
end GaussianPerimeter.VolumeComparison
