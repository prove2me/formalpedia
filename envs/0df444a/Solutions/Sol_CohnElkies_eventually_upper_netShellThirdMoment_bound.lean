-- Prove2me | solution 1 for CohnElkies.eventually_upper_netShellThirdMoment_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/a4726d77-1b7c-43c0-9f1c-f13b32f1acaa

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperPositiveShellThirdMoment_le
import Theorems.Thm_CohnElkies_eventually_upper_shortShellThirdMoment_domination

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ δ : ℝ, ε / 2 ≤ δ →
        upperNetShellThirdMoment ε δ ≤
          (shellLocation ε + 1 + shortEndpoint ε / 100) *
            upperPositiveShellVariance ε δ := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortShellThirdMoment_domination]
    with ε hε hshort
  change 0 < ε at hε
  intro δ hδ
  have hpositive := upperPositiveShellThirdMoment_le
    (δ := δ) hε
  have hnegative := hshort δ hδ
  unfold upperNetShellThirdMoment
  nlinarith
end CohnElkies
