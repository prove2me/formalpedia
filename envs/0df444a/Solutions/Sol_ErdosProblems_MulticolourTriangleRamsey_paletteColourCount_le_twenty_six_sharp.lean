-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteColourCount_le_twenty_six_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/9b8c5561-d522-4731-9889-d9726ed3d2f9

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_one_le_log_nat_of_three_le
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteLogWidth_le_two_log

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 3 ≤ H) :
    (paletteColourCount H : ℝ) ≤
      26 * (H : ℝ) ^ 3 * Real.log (H : ℝ) ^ 3 := by
  let y : ℝ := (H : ℝ) * Real.log (H : ℝ)
  have hlog : 1 ≤ Real.log (H : ℝ) :=
    one_le_log_nat_of_three_le H hH
  have hHreal : (1 : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (show 1 ≤ H by omega)
  have hy : 1 ≤ y := by
    dsimp [y]
    calc
      (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ (H : ℝ) * Real.log (H : ℝ) := by gcongr
  have harg : 0 ≤ 2 * (H : ℝ) * Real.log (H : ℝ) := by
    positivity
  have hceil :
      (⌈2 * (H : ℝ) * Real.log (H : ℝ)⌉₊ : ℝ) ≤
        2 * (H : ℝ) * Real.log (H : ℝ) + 1 :=
    (Nat.ceil_lt_add_one harg).le
  have hm : (saturatedMatrixWidth H : ℝ) ≤ 3 * y := by
    unfold saturatedMatrixWidth
    dsimp [y]
    nlinarith
  have hmsucc : (saturatedMatrixWidth H : ℝ) + 1 ≤ 4 * y := by
    linarith
  have hone : (1 : ℝ) ≤ y ^ 2 := by
    nlinarith [sq_nonneg (y - 1)]
  have hrows : (saturatedMatrixRows H : ℝ) ≤ 13 * y ^ 2 := by
    unfold saturatedMatrixRows
    push_cast
    calc
      (saturatedMatrixWidth H : ℝ) *
          ((saturatedMatrixWidth H : ℝ) + 1) + 1 ≤
        (3 * y) * (4 * y) + y ^ 2 := by
          gcongr
      _ = 13 * y ^ 2 := by ring
  have hwidth := paletteLogWidth_le_two_log H hH
  unfold paletteColourCount
  push_cast
  calc
    (H : ℝ) *
        ((paletteLogWidth H : ℝ) * (saturatedMatrixRows H : ℝ)) ≤
      (H : ℝ) *
        ((2 * Real.log (H : ℝ)) * (13 * y ^ 2)) := by
          gcongr
    _ = 26 * (H : ℝ) ^ 3 * Real.log (H : ℝ) ^ 3 := by
      dsimp [y]
      ring
end ErdosProblems.MulticolourTriangleRamsey
