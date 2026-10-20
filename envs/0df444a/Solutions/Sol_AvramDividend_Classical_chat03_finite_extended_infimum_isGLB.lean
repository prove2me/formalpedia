-- Prove2me | solution 1 for AvramDividend.Classical.chat03_finite_extended_infimum_isGLB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:53:54.500142+00:00
-- url     : https://prove2.me/submissions/376c45ee-edcd-4a8d-9f60-a012536bb8d8

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal

/-!
Translate the exact Formalpedia extended-ENNReal infimum of a predicate's
witness times to the NNReal greatest-lower-bound interface used by
Proved Chat 03 mesh and grid first-passage convergence theorems.
-/
theorem solution
    (p : ℝ≥0 → Prop) (T : ℝ≥0∞)
    (hT : T = ⨅ (t : ℝ≥0) (_ : p t), (t : ℝ≥0∞))
    (hfinite : T ≠ ∞) :
    IsGLB {t : ℝ≥0 | p t} T.toNNReal := by
  constructor
  · intro t ht
    have hle : T ≤ (t : ℝ≥0∞) := by
      rw [hT]
      exact iInf_le_of_le t (iInf_le _ ht)
    have hcast : ((T.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by
      simpa only [ENNReal.coe_toNNReal hfinite] using hle
    exact ENNReal.coe_le_coe.mp hcast
  · intro b hb
    have hle : (b : ℝ≥0∞) ≤ T := by
      rw [hT]
      refine le_iInf fun t => ?_
      refine le_iInf fun ht => ?_
      exact ENNReal.coe_le_coe.mpr (hb ht)
    have hcast : (b : ℝ≥0∞) ≤ ((T.toNNReal : ℝ≥0) : ℝ≥0∞) := by
      simpa only [ENNReal.coe_toNNReal hfinite] using hle
    exact ENNReal.coe_le_coe.mp hcast