-- Prove2me | solution 1 for FD1D.V5.depthTarget_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:46:22.55049+00:00
-- url     : https://prove2.me/submissions/7b4f924a-bc5b-4779-b02e-350665538eb3

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
theorem _root_.solution (m : ℕ) :
    0 < depthTarget m := by
  simp [depthTarget]
end FD1D.V5
