-- Prove2me | solution 1 for FD1D.V5.parameterQuotient_lt_two_mul_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:48:03.274868+00:00
-- url     : https://prove2.me/submissions/87494ddf-fff5-4614-80df-3988724bf7c6

import Definitions.Def_FD1D_Tree
import Definitions.Def_FD1D_V5_Parameters
import Theorems.Thm_FD1D_V5_depthTarget_lt_two_mul_leafCount

set_option autoImplicit true
open FD1D FD1D.V5
noncomputable section
open Filter Asymptotics
namespace FD1D.V5
theorem _root_.solution (m : ℕ) :
    m / parameterA m < 2 * leafCount m := by
  exact (le_max_right 1 (m / parameterA m)).trans_lt
    (depthTarget_lt_two_mul_leafCount m)
end FD1D.V5
