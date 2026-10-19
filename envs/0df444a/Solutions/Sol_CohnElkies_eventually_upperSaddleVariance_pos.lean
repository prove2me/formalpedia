-- Prove2me | solution 1 for CohnElkies.eventually_upperSaddleVariance_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/99c8b5b8-7107-42f8-9958-5d573e255d9e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upperSaddleVariance_bounds
import Theorems.Thm_CohnElkies_upperPositiveShellVariance_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        ∀ ℓ : ℝ, 0 < ℓ →
          ∀ δ : ℝ, ε / 2 ≤ δ →
            0 < upperSaddleVariance ε ℓ δ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upperSaddleVariance_bounds]
    with ε hε hbound
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hδnonnegative : 0 ≤ δ := by
    nlinarith
  have hη : 0 < 2 + δ := by
    linarith
  have hshell :=
    upperPositiveShellVariance_pos hε hδnonnegative
  have hpositive :
      0 < 1 / (2 * (2 + δ)) +
        (99 / 100 : ℝ) *
          upperPositiveShellVariance ε δ := by
    positivity
  exact hpositive.trans_le
    (hbound ℓ hℓ δ hδ).1
end CohnElkies
