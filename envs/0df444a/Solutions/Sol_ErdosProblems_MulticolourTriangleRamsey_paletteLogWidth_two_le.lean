-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteLogWidth_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/afdb3a9a-8fa0-4f83-adb2-b04539040393

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) : 2 ≤ paletteLogWidth H := by
  exact Nat.le_max_left _ _
end ErdosProblems.MulticolourTriangleRamsey
