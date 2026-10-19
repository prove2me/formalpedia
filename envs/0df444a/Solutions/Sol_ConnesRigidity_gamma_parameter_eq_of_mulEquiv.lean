-- Prove2me | solution 1 for ConnesRigidity.gamma_parameter_eq_of_mulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:09.754426+00:00
-- url     : https://prove2.me/submissions/06895c40-7e04-4603-91a3-78e2aa527dc4

import Mathlib
import Definitions.Def_ConnesRigidity
import Theorems.Thm_ConnesRigidity_two_pow_four_injective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
open ConnesRigidity
noncomputable section
open ConnesRigidity
namespace ConnesRigidity
theorem _root_.solution {m n : ℕ}
    (f : gammaGroup m ≃* gammaGroup n) : m = n := by
  apply two_pow_four_injective
  calc
    2 ^ (4 * m) = paperGroupCardinalInvariant.value (gammaGroup m) :=
      (paperInvariant_card m).symm
    _ = paperGroupCardinalInvariant.value (gammaGroup n) :=
      paperGroupCardinalInvariant.value_mulEquiv f
    _ = 2 ^ (4 * n) := paperInvariant_card n
end ConnesRigidity
