-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.bias_nonneg_of_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:53:15.291324+00:00
-- url     : https://prove2.me/submissions/1cb6e82c-5280-4665-8282-e3216319b493

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_orderedBias_nonneg

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hh : 0 < h) (hxy : y ≤ x)
    (ht : discrepancy a p h x y ≤ h / 2) :
    0 ≤ bias a p h x y := by
  rw [bias, if_pos hxy]
  exact orderedBias_nonneg ha hh hxy ht
end FD1D.V5.LocalPolicy
