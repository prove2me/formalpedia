-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceRadius_log_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/bb0f9048-db23-4c2b-a0bc-ca50688b77ce

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleLogRadius_covers_Ici

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
        ∀ r : ℝ,
          saddleSourceRadius ε d ≤ r →
            ∃ u : ℝ,
              1 + ε / 4 ≤ u ∧
                saddleLogRadius ε d u = Real.log r := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_saddleLogRadius_covers_Ici]
    with ε hε hcoverage
  change 0 < ε at hε
  intro d hd r hr
  have hu₀ : -1 < 1 + ε / 4 := by linarith
  apply hcoverage d hd (1 + ε / 4) hu₀ r
  exact hr
end CohnElkies
