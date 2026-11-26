-- Prove2me | solution 1 for FD1D.V5.parameterA_cast_ge_treeDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:47:40.390338+00:00
-- url     : https://prove2.me/submissions/fb614b13-4e6f-411f-9bc8-ec6a524b996d

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_two_thousand_mul_treeDepth_le_parameterA

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) :
    (2000 : ℝ) * treeDepth m ≤ parameterA m := by
  exact_mod_cast two_thousand_mul_treeDepth_le_parameterA hm
end FD1D.V5
