-- Prove2me | solution 2 for DbarRegularity.volume_closedCube
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:52:55.441686+00:00
-- url     : https://prove2.me/submissions/569f8280-a13b-43a3-b067-9f66cccbdbae

import Definitions.Def_DbarRegularity_Setting
import Theorems.Thm_DbarRegularity_closedCube_eq_preimage



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal

theorem volume_closedCube' {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    volume (closedCube a s) = ENNReal.ofReal s ^ d := by
  rw [closedCube_eq_preimage, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  simp

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    volume (closedCube a s) = ENNReal.ofReal s ^ d :=
  volume_closedCube' a s
