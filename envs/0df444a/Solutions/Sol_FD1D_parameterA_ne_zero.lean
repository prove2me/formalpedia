-- Prove2me | solution 1 for FD1D.parameterA_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:26.585711+00:00
-- url     : https://prove2.me/submissions/5ddce15a-7007-4f38-bc4a-cd26fce92127

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_parameterA_pos

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    parameterA m ≠ 0 :=
  (parameterA_pos hm).ne'
end FD1D
