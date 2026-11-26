-- Prove2me | solution 1 for FixedNumerator.determinant_r3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:49:13.24345+00:00
-- url     : https://prove2.me/submissions/7d18f56a-24b9-4bd4-8ad7-28d8baba0081

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_delta_r3_lower


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (N σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ (3 : ℝ))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-1 : ℝ) ∧ 1 - N ^ (-1 : ℝ) ≤ ‖1 + a * w ^ 4‖ :=
  delta_r3_lower hN ha hw hσ
end FixedNumerator
