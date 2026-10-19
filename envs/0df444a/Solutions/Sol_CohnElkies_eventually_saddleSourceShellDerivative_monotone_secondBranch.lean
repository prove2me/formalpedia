-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceShellDerivative_monotone_secondBranch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/3ab76f59-c9af-49db-a9e6-6b857d23bc8f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperPositiveShellVariance_bounds
import Theorems.Thm_CohnElkies_eventually_upper_netShellVariance_bounds
import Theorems.Thm_CohnElkies_saddleSourceShellDerivative_contDiff_one
import Theorems.Thm_CohnElkies_saddleSourceShellDerivative_hasDerivAt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      MonotoneOn (saddleSourceShellDerivative ε)
        (Ici (1 + ε / 2)) := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_upper_netShellVariance_bounds]
    with ε hε horder hnet
  change 0 < ε at hε
  have hcont :
      ContinuousOn (saddleSourceShellDerivative ε)
        (Ici (1 + ε / 2)) :=
    (saddleSourceShellDerivative_contDiff_one hε horder).continuous.continuousOn
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Ici (1 + ε / 2)) hcont
  · intro u hu
    exact (saddleSourceShellDerivative_hasDerivAt
      hε horder u).hasDerivWithinAt
  · intro u hu
    have hthreshold : 1 + ε / 2 ≤ u := by
      have hmem : u ∈ Ici (1 + ε / 2) :=
        interior_subset hu
      exact hmem
    have hδ : ε / 2 ≤ u - 1 := by linarith
    have hδnonneg : 0 ≤ u - 1 := by linarith
    have hvariance :=
      (upperPositiveShellVariance_bounds hε hδnonneg).1
    have hpositive : 0 ≤ upperPositiveShellVariance ε (u - 1) := by
      exact (show
        0 ≤ (1 / 2 : ℝ) * shellLocation ε ^ 2 *
          shellWeight ε *
            Real.exp ((u - 1) * shellLocation ε) by
          positivity [shellWeight_pos ε]).trans hvariance
    have hnetlower := (hnet (u - 1) hδ).1
    nlinarith
end CohnElkies
