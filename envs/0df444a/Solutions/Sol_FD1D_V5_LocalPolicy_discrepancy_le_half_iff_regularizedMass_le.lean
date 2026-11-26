-- Prove2me | solution 1 for FD1D.V5.LocalPolicy.discrepancy_le_half_iff_regularizedMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:44.47794+00:00
-- url     : https://prove2.me/submissions/b30c6c0f-83a5-478b-b606-0ccde0c5aca7

import Definitions.Def_FD1D_V5_LocalPolicy
import Definitions.Def_FD1D_V5_LocalInvariants
import Theorems.Thm_FD1D_V5_LocalPolicy_inventory_nonneg


set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.LocalPolicy
noncomputable section
namespace FD1D.V5.LocalPolicy
theorem _root_.solution
    {a p h : ℝ} {x y : ℕ} (ha : 0 < a) :
    discrepancy a p h x y ≤ h / 2 ↔
      regularizedMass a p x y ≤ h := by
  have hden : 0 < inventory x y + a / 2 := by
    have := inventory_nonneg x y
    linarith
  unfold discrepancy regularizedMass parentMass
  constructor
  · intro ht
    apply (div_le_iff₀ hden).2
    have hmul := (div_le_iff₀ ha).1 ht
    nlinarith
  · intro hZ
    apply (div_le_iff₀ ha).2
    have hmul := (div_le_iff₀ hden).1 hZ
    nlinarith
end FD1D.V5.LocalPolicy
