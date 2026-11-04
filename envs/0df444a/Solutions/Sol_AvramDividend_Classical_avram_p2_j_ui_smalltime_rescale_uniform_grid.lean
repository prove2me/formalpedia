-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_smalltime_rescale_uniform_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:03:57.607201+00:00
-- url     : https://prove2.me/submissions/1e4880da-d974-4c0f-be34-e6be58bad988

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_uniform_mesh_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Small-time first-order real limits yield exactly the horizon-scaled uniform-grid rate. -/
theorem solution
    (T : ℝ≥0) (hT : 0 < T) (Φ : ℝ → ℝ) (L : ℝ)
    (hRate : Tendsto (fun h : ℝ => Φ h / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      Φ ((T : ℝ) / ((n : ℝ) + 1))) atTop (nhds ((T : ℝ) * L)) := by
  have hMesh := avram_p2_a_zero_rate_positive_uniform_mesh_tendsto T hT
  have hComp := hRate.comp hMesh
  have hProd := Filter.Tendsto.const_mul (T : ℝ) hComp
  have hTR : (T : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hT)
  convert hProd using 1
  ext n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Function.comp_def]
  field_simp [hTR, hn]
