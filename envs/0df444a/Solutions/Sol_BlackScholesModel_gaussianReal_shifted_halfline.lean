-- Prove2me | solution 1 for BlackScholesModel.gaussianReal_shifted_halfline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T17:26:16.879693+00:00
-- url     : https://prove2.me/submissions/a808afa0-33a0-44fc-842c-2cdbaaa81644

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Theorems.Thm_BlackScholesModel_gaussianReal_halfline_probs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff ENNReal
open BlackScholesModel

/-- Unit-variance normal half-line probabilities with arbitrary location. -/
theorem solution (a y : ℝ) :
    (gaussianReal a 1).real (Set.Ioi y) = stdNormalCDF (a - y) ∧
    (gaussianReal a 1).real (Set.Iio y) = stdNormalCDF (y - a) := by
  have hId : HasLaw (fun z : ℝ => z)
      (gaussianReal 0 (1 : NNReal))
      (gaussianReal 0 (1 : NNReal)) :=
    ProbabilityTheory.HasLaw.id
  have hLaw : HasLaw (fun z : ℝ => z + a)
      (gaussianReal a (1 : NNReal))
      (gaussianReal 0 (1 : NNReal)) := by
    simpa only [zero_add] using
      (ProbabilityTheory.gaussianReal_add_const hId a)
  have hmeas : Measurable (fun z : ℝ => z + a) := by
    fun_prop
  have hmp : MeasurePreserving (fun z : ℝ => z + a)
      (gaussianReal 0 (1 : NNReal))
      (gaussianReal a (1 : NNReal)) :=
    hLaw.measurePreserving hmeas
  have hUpperSet :
      (fun z : ℝ => z + a) ⁻¹' Set.Ioi y = Set.Ioi (y - a) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have hLowerSet :
      (fun z : ℝ => z + a) ⁻¹' Set.Iio y = Set.Iio (y - a) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iio]
    constructor <;> intro h <;> linarith
  have hUpperMeasure :
      (gaussianReal a (1 : NNReal)) (Set.Ioi y) =
      (gaussianReal 0 (1 : NNReal)) (Set.Ioi (y - a)) := by
    have h := hmp.measure_preimage
      (s := Set.Ioi y) measurableSet_Ioi.nullMeasurableSet
    rw [hUpperSet] at h
    exact h.symm
  have hLowerMeasure :
      (gaussianReal a (1 : NNReal)) (Set.Iio y) =
      (gaussianReal 0 (1 : NNReal)) (Set.Iio (y - a)) := by
    have h := hmp.measure_preimage
      (s := Set.Iio y) measurableSet_Iio.nullMeasurableSet
    rw [hLowerSet] at h
    exact h.symm
  constructor
  · calc
      (gaussianReal a 1).real (Set.Ioi y) =
        (gaussianReal 0 1).real (Set.Ioi (y - a)) := by
          exact congrArg ENNReal.toReal hUpperMeasure
      _ = stdNormalCDF (-(y - a)) :=
        (gaussianReal_halfline_probs (y - a)).1
      _ = stdNormalCDF (a - y) := by congr 1 <;> ring
  · calc
      (gaussianReal a 1).real (Set.Iio y) =
        (gaussianReal 0 1).real (Set.Iio (y - a)) := by
          exact congrArg ENNReal.toReal hLowerMeasure
      _ = stdNormalCDF (y - a) :=
        (gaussianReal_halfline_probs (y - a)).2