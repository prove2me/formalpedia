-- Prove2me | solution 1 for FD1D.leafCount_cast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:50.532706+00:00
-- url     : https://prove2.me/submissions/5db0f0b6-8279-40d4-b860-f48c29614552

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_leafCount_cast_pos

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    (leafCount m : ℝ) ≠ 0 :=
  (leafCount_cast_pos m).ne'
end FD1D
