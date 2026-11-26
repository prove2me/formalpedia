-- Prove2me | solution 1 for FD1D.depthTarget_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:15:54.799691+00:00
-- url     : https://prove2.me/submissions/b47a8fe6-48f9-46fd-9890-c4829f484b61

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.policyA_eq_parameterA
attribute [local simp] FD1D.natFloor_parameterRatio

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    depthTarget m ≤ m := by
  simp only [depthTarget, max_le_iff]
  exact ⟨hm, Nat.div_le_self _ _⟩
end FD1D
