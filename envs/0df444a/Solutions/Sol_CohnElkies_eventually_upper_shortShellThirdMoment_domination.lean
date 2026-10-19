-- Prove2me | solution 1 for CohnElkies.eventually_upper_shortShellThirdMoment_domination
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/f69663e8-e6e4-4261-99a0-adbcbff76724

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upper_shortMargin_positive
import Theorems.Thm_CohnElkies_eventually_upper_shortShellVariance_domination
import Theorems.Thm_CohnElkies_upperShortShellThirdMoment_le

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
        upperShortShellThirdMoment ε δ ≤
          (shortEndpoint ε / 100) *
            upperPositiveShellVariance ε δ := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_shortMargin_positive,
      eventually_upper_shortShellVariance_domination]
    with ε hε horder hmargin hdom
  change 0 < ε at hε
  intro δ hδ
  have ha₀ : 0 < shortCutoff ε := by
    unfold shortCutoff
    positivity
  have hA : 0 ≤ shortEndpoint ε :=
    (ha₀.trans_le horder).le
  have hthird := upperShortShellThirdMoment_le
    (δ := δ) hε horder
    (fun a ha => by
      have h := hmargin a ha
      linarith)
  calc
    upperShortShellThirdMoment ε δ ≤
      shortEndpoint ε * upperShortShellVariance ε δ := hthird
    _ ≤ shortEndpoint ε *
      ((1 / 100 : ℝ) *
        upperPositiveShellVariance ε δ) :=
      mul_le_mul_of_nonneg_left (hdom δ hδ) hA
    _ = (shortEndpoint ε / 100) *
      upperPositiveShellVariance ε δ := by
        ring
end CohnElkies
