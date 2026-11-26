-- Prove2me | solution 1 for FirstPassageLinearTransport.normalized_card_shellMultiplicativeHit_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:22.438442+00:00
-- url     : https://prove2.me/submissions/c5940fac-21bf-4635-9e2c-77612c31b759

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_card_shellMultiplicativeHit
import Theorems.Thm_FirstPassageLinearTransport_reciprocal_finite_multiplicative_maximum


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {u : ℝ} (hu : 1 ≤ u) {M : ℕ} (hM : 0 < M)
    (hlog : Real.log u ≤
      reciprocalMaximumEpsilon * (M : ℝ) * Real.log 3) :
    (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (M : ℝ)) ≤
      ((shellMultiplicativeHit M u).card : ℝ) / (2 : ℝ) ^ M ∧
    ((shellMultiplicativeHit M u).card : ℝ) / (2 : ℝ) ^ M ≤ u⁻¹ := by
  rw [card_shellMultiplicativeHit]
  exact reciprocal_finite_multiplicative_maximum hu hM hlog
end FirstPassageLinearTransport
