-- Prove2me | solution 1 for FD1D.V5.leafCount_cast_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:47.564944+00:00
-- url     : https://prove2.me/submissions/cd752b6a-bb99-4fbf-a7c1-4df6752933a9

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_leafCount_pos

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution (m : ℕ) :
    0 < (leafCount m : ℝ) := by
  exact_mod_cast leafCount_pos m
end FD1D.V5
