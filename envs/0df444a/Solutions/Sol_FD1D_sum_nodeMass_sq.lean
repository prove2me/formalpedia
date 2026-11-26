-- Prove2me | solution 1 for FD1D.sum_nodeMass_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:35.21974+00:00
-- url     : https://prove2.me/submissions/a8d6b7de-0a61-4f5a-af1f-f1c33ff50839

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_weightedLevel_zero
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.weightedLevel_zero

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution (d : ℕ) :
    ∑ v : DyadicNode d, (nodeMass d v) ^ 2 = ((2 : ℝ) ^ d)⁻¹ := by
  simp [nodeMass]
  field_simp
end FD1D
