-- Prove2me | solution 1 for CohnElkies.eventually_tendsto_saddleLogRadius_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/bcbe3db9-bea6-409e-969a-0d0d6a756516

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleSourceShellDerivative_monotone_secondBranch
import Theorems.Thm_CohnElkies_tendsto_saddleLogRadius_atTop_of_shell_monotone

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
      ∀ d : ℕ, 0 < d →
        Tendsto (saddleLogRadius ε d) atTop atTop := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_saddleSourceShellDerivative_monotone_secondBranch]
    with ε hε horder hmono
  change 0 < ε at hε
  intro d hd
  exact tendsto_saddleLogRadius_atTop_of_shell_monotone
    hε horder hd hmono
end CohnElkies
