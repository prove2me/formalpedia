-- Prove2me | solution 1 for FD1D.one_le_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:49.475549+00:00
-- url     : https://prove2.me/submissions/3fd46757-e125-449e-a477-9eb7e484c52d

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_leafCount_pos

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    1 ≤ leafCount m :=
  (leafCount_pos m)
end FD1D
