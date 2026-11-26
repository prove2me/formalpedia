-- Prove2me | solution 1 for FixedNumerator.determinant_r1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:48:56.236119+00:00
-- url     : https://prove2.me/submissions/a2032c4c-c2a0-4f08-a7d6-6ea36a3a3328

module
public import Definitions.Def_FixedNumerator
public import Definitions.Def_FixedNumerator_Solution
public import Theorems.Thm_FixedNumerator_delta_r1_lower


set_option autoImplicit true
@[expose] public section
public section
open Complex Finset Filter Asymptotics Topology
open scoped ContDiff
noncomputable section
open FixedNumerator
namespace FixedNumerator
theorem _root_.solution (N σ : ℝ) (hN : 1 < N) (a w : ℂ) (ha : ‖a‖ ≤ N ^ ((3 : ℝ) / 2))
    (hw : ‖w‖ = N ^ (-σ)) (hσ : 1 ≤ σ) :
    0 < 1 - N ^ (-(1 : ℝ) / 2) ∧ 1 - N ^ (-(1 : ℝ) / 2) ≤ ‖1 + a * w ^ 2‖ :=
  delta_r1_lower hN ha hw hσ
end FixedNumerator
