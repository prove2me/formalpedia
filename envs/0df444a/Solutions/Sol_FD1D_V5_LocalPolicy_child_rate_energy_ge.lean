-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.child_rate_energy_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:14.895364+00:00
-- url     : https://prove2.me/submissions/a1d051ed-63d3-4564-ab9e-e1a37fdb30a6

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_child_rates_nonneg
import Theorems.Thm_FD1D_V5_LocalPolicy_child_rate_average_ge

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ}
    (ha : 0 < a) (hp : 0 < p) (hh : 0 < h)
    (ht : discrepancy a p h x y ≤ h / 2) :
    h ^ 2 ≤
      (rateLeft a p h x y ^ 2 + rateRight a p h x y ^ 2) / 2 := by
  have havg := child_rate_average_ge ha hp hh ht
  have hnonneg := child_rates_nonneg ha hp hh ht
  nlinarith [sq_nonneg
    (rateLeft a p h x y - rateRight a p h x y)]
end FD1D.V5.LocalPolicy
