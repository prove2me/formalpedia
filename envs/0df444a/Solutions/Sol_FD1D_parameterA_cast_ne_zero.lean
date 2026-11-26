-- Prove2me | solution 1 for FD1D.parameterA_cast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:33.032019+00:00
-- url     : https://prove2.me/submissions/93b41274-8645-4c89-a1a5-f617662a6319

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_parameterA_cast_pos

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    (parameterA m : ℝ) ≠ 0 :=
  (parameterA_cast_pos hm).ne'
end FD1D
