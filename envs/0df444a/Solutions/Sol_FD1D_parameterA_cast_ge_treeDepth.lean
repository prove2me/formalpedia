-- Prove2me | solution 1 for FD1D.parameterA_cast_ge_treeDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:59:46.499911+00:00
-- url     : https://prove2.me/submissions/0576ba7c-cde8-49bd-866e-d4d0f2638cf2

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_two_hundred_mul_treeDepth_le_parameterA

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    (200 : ℝ) * treeDepth m ≤ parameterA m := by
  exact_mod_cast two_hundred_mul_treeDepth_le_parameterA hm
end FD1D
