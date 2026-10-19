-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteColourCount_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/b8fc9c4e-81de-4225-8736-62a3c9cf453f

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution : paletteColourCount 3 = 342 := by
  have hlo : (1 : ℝ) < Real.log 3 := by
    nlinarith [Real.log_three_gt_d9]
  have hhi : Real.log (3 : ℝ) < 7 / 6 := by
    nlinarith [Real.log_three_lt_d9]
  have ha : ⌈Real.log (3 : ℝ)⌉₊ = 2 := by
    apply (Nat.ceil_eq_iff (by norm_num : (2 : ℕ) ≠ 0)).mpr
    constructor <;> norm_num <;> linarith
  have hm : ⌈(6 : ℝ) * Real.log (3 : ℝ)⌉₊ = 7 := by
    apply (Nat.ceil_eq_iff (by norm_num : (7 : ℕ) ≠ 0)).mpr
    constructor <;> norm_num <;> nlinarith
  norm_num [paletteColourCount, paletteLogWidth,
    saturatedMatrixRows, saturatedMatrixWidth, ha, hm]
end ErdosProblems.MulticolourTriangleRamsey
