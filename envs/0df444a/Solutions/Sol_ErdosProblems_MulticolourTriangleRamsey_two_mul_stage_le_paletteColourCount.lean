-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.two_mul_stage_le_paletteColourCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/2f524f2c-fa06-4960-a4e7-d8258a8c5efb

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteLogWidth_two_le

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) :
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
end ErdosProblems.MulticolourTriangleRamsey
