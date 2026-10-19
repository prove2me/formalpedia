-- Prove2me | solution 1 for CohnElkies.eventually_upperSaddleVariance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/f3a5d57b-325d-464f-b8d6-41b8e2e32297

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_netShellVariance_bounds
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds

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
            1 / (2 * (2 + δ)) +
                (99 / 100 : ℝ) *
                  upperPositiveShellVariance ε δ ≤
              upperSaddleVariance ε ℓ δ ∧
            upperSaddleVariance ε ℓ δ ≤
              (1 / (2 * (2 + δ)) +
                1 / (ℓ * (2 + δ) ^ 2)) +
                  upperPositiveShellVariance ε δ := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_netShellVariance_bounds]
    with ε hε hnet
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hη : 0 < 2 + δ := by
    nlinarith
  obtain ⟨hγlow, hγhigh⟩ :=
    upperGammaVariance_bounds hℓ hη
  obtain ⟨hslow, hshigh⟩ :=
    hnet δ hδ
  unfold upperSaddleVariance
  exact ⟨add_le_add hγlow hslow,
    add_le_add hγhigh hshigh⟩
end CohnElkies
