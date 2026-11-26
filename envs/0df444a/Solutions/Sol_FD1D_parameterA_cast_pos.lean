-- Prove2me | solution 1 for FD1D.parameterA_cast_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:50.284823+00:00
-- url     : https://prove2.me/submissions/8a14b9e7-63f8-465a-9424-0343753fa2e0

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_parameterA_pos

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    0 < (parameterA m : ℝ) := by
  exact_mod_cast parameterA_pos hm
end FD1D
