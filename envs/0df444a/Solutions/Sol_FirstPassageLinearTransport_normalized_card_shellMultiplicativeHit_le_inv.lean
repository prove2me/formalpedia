-- Prove2me | solution 1 for FirstPassageLinearTransport.normalized_card_shellMultiplicativeHit_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:13:15.255801+00:00
-- url     : https://prove2.me/submissions/ab523e6d-e3c0-4104-8b91-2db2e67ea324

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_card_shellMultiplicativeHit
import Theorems.Thm_FirstPassageLinearTransport_normalized_multiplicativeHitCount_le_inv


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {u : ℝ} (hu : 0 < u) (M : ℕ) :
    ((shellMultiplicativeHit M u).card : ℝ) / (2 : ℝ) ^ M ≤ u⁻¹ := by
  rw [card_shellMultiplicativeHit]
  exact normalized_multiplicativeHitCount_le_inv hu M
end FirstPassageLinearTransport
