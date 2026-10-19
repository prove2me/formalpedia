-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.log_le_paletteLogWidth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/1d8ab60e-df43-4db9-8982-00009331737e

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) :
    Real.log (H : ℝ) ≤ (paletteLogWidth H : ℝ) := by
  calc
    Real.log (H : ℝ) ≤ (⌈Real.log (H : ℝ)⌉₊ : ℝ) :=
      Nat.le_ceil _
    _ ≤ (paletteLogWidth H : ℝ) := by
      exact_mod_cast (Nat.le_max_right 2 ⌈Real.log (H : ℝ)⌉₊)
end ErdosProblems.MulticolourTriangleRamsey
