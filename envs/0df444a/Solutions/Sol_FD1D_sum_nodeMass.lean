-- Prove2me | solution 1 for FD1D.sum_nodeMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:50:13.748306+00:00
-- url     : https://prove2.me/submissions/b4fb16fa-a6ea-4696-8c1d-32c432e7cd09

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const



set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution (d : ℕ) :
    ∑ v : DyadicNode d, nodeMass d v = 1 := by
  simp [nodeMass]
end FD1D
