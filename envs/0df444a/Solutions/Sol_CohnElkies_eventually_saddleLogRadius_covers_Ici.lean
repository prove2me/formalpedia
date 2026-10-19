-- Prove2me | solution 1 for CohnElkies.eventually_saddleLogRadius_covers_Ici
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/ba789eb3-08af-4a11-a935-9008c1376593

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_tendsto_saddleLogRadius_atTop
import Theorems.Thm_CohnElkies_saddleLogRadius_covers_Ici

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
        ∀ u₀ : ℝ, -1 < u₀ →
          ∀ r : ℝ,
            Real.exp (saddleLogRadius ε d u₀) ≤ r →
              ∃ u : ℝ, u₀ ≤ u ∧
                saddleLogRadius ε d u = Real.log r := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_tendsto_saddleLogRadius_atTop]
    with ε hε horder htop
  change 0 < ε at hε
  intro d hd u₀ hu₀ r hr
  exact saddleLogRadius_covers_Ici
    hε horder hd hu₀ (htop d hd) hr
end CohnElkies
