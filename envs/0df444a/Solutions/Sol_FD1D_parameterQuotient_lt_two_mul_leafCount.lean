-- Prove2me | solution 1 for FD1D.parameterQuotient_lt_two_mul_leafCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:22:20.524789+00:00
-- url     : https://prove2.me/submissions/1716a4b1-0f51-4118-90c6-39056be34347

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Parameters
import Theorems.Thm_FD1D_depthTarget_lt_two_mul_leafCount

set_option autoImplicit true
open FD1D
noncomputable section
open Filter Asymptotics
namespace FD1D
theorem _root_.solution (m : ℕ) :
    m / parameterA m < 2 * leafCount m := by
  exact (le_max_right 1 (m / parameterA m)).trans_lt
    (depthTarget_lt_two_mul_leafCount m)
end FD1D
