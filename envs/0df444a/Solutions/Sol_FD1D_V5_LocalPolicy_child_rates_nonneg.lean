-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.child_rates_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:09.305795+00:00
-- url     : https://prove2.me/submissions/a80fbc21-5208-4d4b-a1b0-01a2fd8166b5

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_child_invariants

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 ≤ rateLeft a p h x y ∧ 0 ≤ rateRight a p h x y := by
  have hchild := child_invariants ha hp hh ht
  have hZL : 0 ≤ regularizedMassLeft a p x y := by
    unfold regularizedMassLeft
    positivity
  have hZR : 0 ≤ regularizedMassRight a p x y := by
    unfold regularizedMassRight
    positivity
  exact ⟨hZL.trans hchild.2.1, hZR.trans hchild.2.2.2⟩
end FD1D.V5.LocalPolicy
