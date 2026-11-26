-- Prove2me | solution 1 for FixedNumerator.countAbs_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:42:29.003653+00:00
-- url     : https://prove2.me/submissions/14037eb1-f6b1-4251-993c-6bfd7c2a6c59

module
public import Definitions.Def_FixedNumerator_Determinant
public import Definitions.Def_FixedNumerator_Sharp

set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (a : ℕ → ℂ) (x : ℝ) : 0 ≤ countAbs a x :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _
end FixedNumerator
