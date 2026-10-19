-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteColourCount_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/57d130b8-9333-4e9a-8b21-e21e33244c39

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {H H' : ℕ}
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
end ErdosProblems.MulticolourTriangleRamsey
