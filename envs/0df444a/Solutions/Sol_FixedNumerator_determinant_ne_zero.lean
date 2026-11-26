-- Prove2me | solution 1 for FixedNumerator.determinant_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:35.141056+00:00
-- url     : https://prove2.me/submissions/cbc518ec-e092-400e-acfc-8bc1956bdf30

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_det_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (N A σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) (h : A < k * σ) : 1 + a * w ^ k ≠ 0 :=
  det_ne_zero hN ha hw k h
end FixedNumerator
