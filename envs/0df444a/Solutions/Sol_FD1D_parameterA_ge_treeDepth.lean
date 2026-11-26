-- Prove2me | solution 1 for FD1D.parameterA_ge_treeDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:35.850945+00:00
-- url     : https://prove2.me/submissions/9199dcb9-818e-44ed-9f5f-4bb584da6ddf

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_two_hundred_mul_treeDepth_le_parameterA

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    parameterA m ≥ 200 * treeDepth m :=
  two_hundred_mul_treeDepth_le_parameterA hm
end FD1D
