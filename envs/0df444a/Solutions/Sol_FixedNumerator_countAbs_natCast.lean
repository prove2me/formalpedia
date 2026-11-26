-- Prove2me | solution 1 for FixedNumerator.countAbs_natCast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:42:46.964794+00:00
-- url     : https://prove2.me/submissions/7a219a80-12a7-453f-a827-9596916bab8d

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
theorem _root_.solution (a : ℕ → ℂ) (X : ℕ) : countAbs a X = ∑ n ∈ Icc 1 X, ‖a n‖ := by
  simp [countAbs]
end FixedNumerator
