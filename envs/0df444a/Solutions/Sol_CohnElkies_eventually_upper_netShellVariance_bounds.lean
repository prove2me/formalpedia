-- Prove2me | solution 1 for CohnElkies.eventually_upper_netShellVariance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/074a2794-8810-4185-b9f2-184678acf0fb

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_upperShortShellVariance_nonneg
import Theorems.Thm_CohnElkies_eventually_upper_shortShellVariance_domination

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
        (99 / 100 : ℝ) *
            upperPositiveShellVariance ε δ ≤
          upperNetShellVariance ε δ ∧
        upperNetShellVariance ε δ ≤
          upperPositiveShellVariance ε δ := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shortMargin_positive,
      eventually_upper_shortShellVariance_domination]
    with ε hε horder hmargin hdom
  change 0 < ε at hε
  intro δ hδ
  have hnonneg := upperShortShellVariance_nonneg
    (δ := δ) hε horder
    (fun a ha => by
      have h := hmargin a ha
      nlinarith)
  have hupper := hdom δ hδ
  unfold upperNetShellVariance
  constructor <;> nlinarith
end CohnElkies
