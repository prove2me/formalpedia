-- Prove2me | solution 1 for FD1D.nodeMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:28.137126+00:00
-- url     : https://prove2.me/submissions/62f68f8f-1c13-4904-aaaa-c861b87d4aff

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution (d : ℕ) (v : DyadicNode d) :
    0 < nodeMass d v := by
  simp [nodeMass]
end FD1D
