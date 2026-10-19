-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.stage_mul_paletteWidth_le_matrixWidth_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/f23deb94-30cb-4f93-9850-9d8161deb9fb

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteLogWidth_le_two_log

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 3 ≤ H) :
    H * paletteLogWidth H ≤ saturatedMatrixWidth H := by
  have hpalette := paletteLogWidth_le_two_log H hH
  have hmatrix :
      2 * (H : ℝ) * Real.log (H : ℝ) ≤
        (saturatedMatrixWidth H : ℝ) := by
    exact Nat.le_ceil _
  have hscaled :=
    mul_le_mul_of_nonneg_left hpalette (show (0 : ℝ) ≤ H by positivity)
  have hreal :
      ((H * paletteLogWidth H : ℕ) : ℝ) ≤
        (saturatedMatrixWidth H : ℝ) := by
    push_cast
    calc
      (H : ℝ) * (paletteLogWidth H : ℝ) ≤
          (H : ℝ) * (2 * Real.log (H : ℝ)) := hscaled
      _ = 2 * (H : ℝ) * Real.log (H : ℝ) := by ring
      _ ≤ (saturatedMatrixWidth H : ℝ) := hmatrix
  exact_mod_cast hreal
end ErdosProblems.MulticolourTriangleRamsey
