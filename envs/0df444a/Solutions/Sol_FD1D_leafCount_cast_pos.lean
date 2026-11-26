-- Prove2me | solution 1 for FD1D.leafCount_cast_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:05.302494+00:00
-- url     : https://prove2.me/submissions/870c6778-f865-44e4-b2bf-1db43f5b6e29

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_leafCount_pos

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    0 < (leafCount m : ℝ) := by
  exact_mod_cast leafCount_pos m
end FD1D
