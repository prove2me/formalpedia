-- Prove2me | solution 1 for CohnElkies.stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:21.360486+00:00
-- url     : https://prove2.me/submissions/cadcea89-f276-4b5e-a5e1-91b0992e3c94

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_stripRegularizedHolomorphicPoissonKernel_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    HasDerivAt
      (fun w : ℂ => stripRegularizedHolomorphicPoissonKernel ℓ w y)
      (stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y) z := by
  simpa [stripRegularizedHolomorphicPoissonKernelDeriv] using!
    stripRegularizedHolomorphicPoissonKernel_hasDerivAt hℓ hz y
end CohnElkies
