-- Prove2me | solution 1 for FD1D.leafCount_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:50.063729+00:00
-- url     : https://prove2.me/submissions/cb5e11fa-bee9-4f5b-85f8-54ec48f7ba21

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_leafCount_pos

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    leafCount m ≠ 0 :=
  (leafCount_pos m).ne'
end FD1D
