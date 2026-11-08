-- Prove2me | solution 1 for FakeAccountsAudit.DefensivePurchase.range_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:44:42.646708+00:00
-- url     : https://prove2.me/submissions/c538c047-34c6-4589-a5b4-5a9815efe74a

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting
set_option autoImplicit false

theorem solution (P : FakeAccounts.Platform.Params)
    (htau : P.tau < 1) (hl : 0 < P.l) (d : ℝ) :
    d ≤ FakeAccounts.Platform.d2 P ↔
      FakeAccounts.Platform.price P d ≤ FakeAccounts.Platform.eta2 P := by
  unfold FakeAccounts.Platform.d2 FakeAccounts.Platform.price
  have h : 0 < 1 - P.tau := by linarith
  rw [← le_sub_iff_add_le', div_le_iff₀ h, mul_comm]
