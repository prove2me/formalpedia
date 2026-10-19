-- Prove2me | solution 1 for CohnElkies.eventually_upperSaddleDamping_gamma_add_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/6822bcc7-6e27-4efb-bfe2-380ab5b20311

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_shortShell_domination

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
            ∀ T : ℝ,
              upperGammaDamping ℓ (2 + δ) T +
                (99 / 100 : ℝ) *
                  positiveShellDamping ε ℓ δ T ≤
                upperSaddleDamping ε ℓ δ T := by
  filter_upwards [eventually_upper_shortShell_domination]
    with ε hdom
  intro ℓ hℓ δ hδ T
  have hshort := hdom ℓ hℓ.le δ hδ T
  unfold upperSaddleDamping
  linarith
end CohnElkies
