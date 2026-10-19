-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceContourDamping_secondBranch_min_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/8e2122e0-d664-4a36-af04-c8c22ccf5b1c

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaDamping_lower_bound
import Theorems.Thm_CohnElkies_eventually_upperSaddleDamping_gamma_add_shell
import Theorems.Thm_CohnElkies_positiveShellDamping_nonneg

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            (ℓ / (8 * Real.exp 1)) *
                min (T ^ 2 / (2 + δ)) |T| ≤
              saddleSourceContourDamping ε ℓ (1 + δ) T := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upperSaddleDamping_gamma_add_shell]
    with ε hε hdom
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T
  have hδ0 : 0 ≤ δ := by nlinarith
  have hη : 0 < 2 + δ := by linarith
  have hgamma := upperGammaDamping_lower_bound
    hℓ hη T
  have hshell : 0 ≤ (99 / 100 : ℝ) *
      positiveShellDamping ε ℓ δ T := by
    positivity [positiveShellDamping_nonneg
      (ε := ε) (δ := δ) (T := T) hℓ.le]
  rw [saddleSourceContourDamping_eq_secondBranch]
  linarith [hdom ℓ hℓ δ hδ T]
end CohnElkies
