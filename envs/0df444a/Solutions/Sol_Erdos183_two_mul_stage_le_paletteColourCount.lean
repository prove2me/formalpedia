-- Prove2me | solution 1 for Erdos183.two_mul_stage_le_paletteColourCount
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:30:35.068306+00:00
-- url     : https://prove2.me/submissions/de1a8f6c-da04-4bcf-8d01-af3e9880d861

import Definitions.Def_erdos183_core
import Mathlib.Algebra.Order.Ring.Nat
import Theorems.Thm_Erdos183_paletteLogWidth_two_le

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution (H : ℕ) :
    2 * H ≤ paletteColourCount H := by
  have hrows : 1 ≤ saturatedMatrixRows H := by
    simp [saturatedMatrixRows]
  have hfactor : 2 ≤ paletteLogWidth H * saturatedMatrixRows H := by
    calc
      2 = 2 * 1 := by simp
      _ ≤ paletteLogWidth H * saturatedMatrixRows H :=
        Nat.mul_le_mul (paletteLogWidth_two_le H) hrows
  unfold paletteColourCount
  calc
    2 * H = H * 2 := by omega
    _ ≤ H * (paletteLogWidth H * saturatedMatrixRows H) :=
      Nat.mul_le_mul_left H hfactor
