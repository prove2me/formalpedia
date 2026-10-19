-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows_adjacent_scaled_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/96a81df7-0ccd-487f-a982-5b7ca143866e

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteLogWidth_two_le
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_stageWidths_succ_le
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_stage_mul_paletteWidth_le_matrixWidth_sharp

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 3 ≤ H) :
    H * saturatedMatrixRows (H + 1) ≤
      (H + 14) * saturatedMatrixRows H := by
  let w := saturatedMatrixWidth H
  let a := paletteLogWidth H
  have ha : 2 ≤ a := by
    simpa [a] using paletteLogWidth_two_le H
  have hwa : H * a ≤ w := by
    simpa [a, w] using stage_mul_paletteWidth_le_matrixWidth_sharp H hH
  have hthreea : 3 * a ≤ w :=
    (Nat.mul_le_mul_right a hH).trans hwa
  have hnext : saturatedMatrixWidth (H + 1) ≤ w + 4 * a := by
    have hwidth := (stageWidths_succ_le H (by omega)).2
    change saturatedMatrixWidth (H + 1) ≤ w + 2 * a + 4 at hwidth
    exact hwidth.trans (by omega)
  have hrows : saturatedMatrixRows (H + 1) ≤
      (w + 4 * a) * (w + 4 * a + 1) + 1 := by
    unfold saturatedMatrixRows
    gcongr
  calc
    H * saturatedMatrixRows (H + 1) ≤
        H * ((w + 4 * a) * (w + 4 * a + 1) + 1) :=
      Nat.mul_le_mul_left H hrows
    _ = H * (w * (w + 1) + 1) +
        H * a * (8 * w + 16 * a + 4) := by ring
    _ ≤ H * (w * (w + 1) + 1) +
        14 * (w * (w + 1) + 1) :=
      Nat.add_le_add_left (by
        calc
          H * a * (8 * w + 16 * a + 4) ≤
              w * (8 * w + 16 * a + 4) :=
            Nat.mul_le_mul_right _ hwa
          _ ≤ w * (14 * w + 4) :=
            Nat.mul_le_mul_left w (by omega)
          _ ≤ 14 * (w * (w + 1) + 1) := by nlinarith) _
    _ = (H + 14) * saturatedMatrixRows H := by
      simp [w, saturatedMatrixRows]
      ring
end ErdosProblems.MulticolourTriangleRamsey
