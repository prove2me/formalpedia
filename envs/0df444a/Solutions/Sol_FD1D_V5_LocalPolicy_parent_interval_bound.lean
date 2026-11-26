-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.parent_interval_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:50:33.451481+00:00
-- url     : https://prove2.me/submissions/fccf966d-2593-4588-9137-e37fec967546

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_discrepancy_le_half_iff_regularizedMass_le
import Theorems.Thm_FD1D_V5_LocalPolicy_inventory_nonneg


set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a)
    (ht : discrepancy a p h x y ≤ h / 2) :
    p ≤ h * (inventory x y + a / 2) := by
  have hden : 0 < inventory x y + a / 2 := by
    have := inventory_nonneg x y
    linarith
  have hZ :=
    (discrepancy_le_half_iff_regularizedMass_le ha).1 ht
  have := (div_le_iff₀ hden).1 hZ
  nlinarith
end FD1D.V5.LocalPolicy
