-- Prove2me | solution 1 for FixedNumerator.determinant_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:26.63765+00:00
-- url     : https://prove2.me/submissions/a6f9f44a-e7aa-4e1e-bd89-eae9476990f1

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_det_lower


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (N A σ : ℝ) (hN : 0 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ A)
    (hw : ‖w‖ = N ^ (-σ)) (k : ℕ) : 1 - N ^ (A - k * σ) ≤ ‖1 + a * w ^ k‖ :=
  det_lower hN ha hw k
end FixedNumerator
