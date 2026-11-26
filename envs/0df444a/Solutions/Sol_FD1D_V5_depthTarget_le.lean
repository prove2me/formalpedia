-- Prove2me | solution 1 for FD1D.V5.depthTarget_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:17.124506+00:00
-- url     : https://prove2.me/submissions/020b49ba-fff4-4d2d-abf8-cdcb40919069

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    depthTarget m ≤ m := by
  simp only [depthTarget, max_le_iff]
  exact ⟨hm, Nat.div_le_self _ _⟩
end FD1D.V5
