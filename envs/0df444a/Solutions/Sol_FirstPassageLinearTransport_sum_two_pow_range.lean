-- Prove2me | solution 1 for FirstPassageLinearTransport.sum_two_pow_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:18.135888+00:00
-- url     : https://prove2.me/submissions/257f3ddd-68e7-44f9-a6d8-e7d9411de625

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (L : ℕ) :
    ∑ j ∈ Finset.range L, (2 : ℝ) ^ j = (2 : ℝ) ^ L - 1 := by
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  norm_num
end FirstPassageLinearTransport
