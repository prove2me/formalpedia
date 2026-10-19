-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth_le_stage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/ff565647-74bb-4166-ae26-7eb3ee94998d

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 2 ≤ H) :
    paletteLogWidth H ≤ H := by
  unfold paletteLogWidth
  apply max_le
  · exact hH
  · apply Nat.ceil_le.mpr
    have hpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    have hlog := Real.log_le_sub_one_of_pos hpos
    exact hlog.trans (by linarith)
end ErdosProblems.MulticolourTriangleRamsey
