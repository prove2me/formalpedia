-- Prove2me | solution 1 for AvramDividend.Classical.causal_weighted_BCF_extension_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T07:06:37.885224+00:00
-- url     : https://prove2.me/submissions/8d852866-1ddd-4f2d-9627-95250dd7723f

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exponential reweighting of a BCF has a continuous real-time extension. -/
theorem solution
    (f : BoundedContinuousFunction ℝ≥0 ℝ) (w : ℝ) :
    Continuous (fun x : ℝ => Real.exp (w * x) *
      f ⟨max x 0, le_max_right x 0⟩) := by
  have hmax : Continuous (fun x : ℝ =>
      (⟨max x 0, le_max_right x 0⟩ : ℝ≥0)) :=
    (continuous_id.max continuous_const).subtype_mk _
  have hf : Continuous (fun x : ℝ =>
      f ⟨max x 0, le_max_right x 0⟩) := f.continuous.comp hmax
  have he : Continuous (fun x : ℝ => Real.exp (w * x)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact he.mul hf
