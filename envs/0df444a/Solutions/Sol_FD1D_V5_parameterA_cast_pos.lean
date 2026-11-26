-- Prove2me | solution 1 for FD1D.V5.parameterA_cast_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:06:23.10005+00:00
-- url     : https://prove2.me/submissions/40082a74-ebc5-4548-9239-2baaf4d58077

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_parameterA_pos

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    0 < (parameterA m : ℝ) := by
  exact_mod_cast parameterA_pos hm
end FD1D.V5
