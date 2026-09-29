-- Prove2me | solution 1 for Erdos183.paletteColourCount_mono
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:29:53.261758+00:00
-- url     : https://prove2.me/submissions/b239e084-392f-4ff7-a50f-ede475e02694

import Definitions.Def_erdos183_core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution {H H' : ℕ}
    (hH : 1 ≤ H) (hHH' : H ≤ H') :
    paletteColourCount H ≤ paletteColourCount H' := by
  have hpos : (0 : ℝ) < H := by
    exact_mod_cast (by omega : 0 < H)
  have hreal : (H : ℝ) ≤ H' := by
    exact_mod_cast hHH'
  have hlog : Real.log (H : ℝ) ≤ Real.log (H' : ℝ) :=
    Real.log_le_log hpos hreal
  have hlognonneg : 0 ≤ Real.log (H : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hH)
  have hwidth : saturatedMatrixWidth H ≤ saturatedMatrixWidth H' := by
    unfold saturatedMatrixWidth
    apply Nat.ceil_le_ceil
    gcongr
  unfold paletteColourCount
  apply Nat.mul_le_mul hHH'
  apply Nat.mul_le_mul
  · exact max_le_max_left 2 (Nat.ceil_le_ceil hlog)
  · unfold saturatedMatrixRows
    gcongr
