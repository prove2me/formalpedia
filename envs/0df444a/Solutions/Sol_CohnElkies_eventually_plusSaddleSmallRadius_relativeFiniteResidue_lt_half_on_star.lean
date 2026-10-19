-- Prove2me | solution 1 for CohnElkies.eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half_on_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/2fc81db3-25ba-4b61-a660-d68b51c0937e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallRadiusVariable_nonneg
import Theorems.Thm_CohnElkies_exists_eventually_y_star_le_log_eighth_add
import Theorems.Thm_CohnElkies_eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half
import Theorems.Thm_CohnElkies_tendsto_saddleResidue_dimension_half

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
    {ε : ℝ}
    (hε : 0 < ε)
    (horder : shortCutoff ε ≤ shortEndpoint ε) :
    ∀ᶠ d : ℕ in atTop,
      ∀ r : ℝ,
        0 ≤ r → r ≤ saddleSmallRadiusStar ε d →
          let ℓ : ℝ := (d : ℝ) / 2
          let y : ℝ := saddleSmallRadiusVariable ε r
          Real.exp y *
            |(∑ n ∈ Finset.range
                (saddleSmallResidueTruncation ℓ + 1),
              ((-y) ^ n / (n.factorial : ℝ)) *
                plusSaddleSmallRadiusCoefficient ε ℓ n) -
              Real.exp (-y)| < 1 / 2 := by
  obtain ⟨C, hC, hstar⟩ :=
    exists_eventually_y_star_le_log_eighth_add hε horder
  have hrelative :=
    eventually_plusSaddleSmallRadius_relativeFiniteResidue_lt_half
      hε horder hC
  have hdimension :=
    tendsto_saddleResidue_dimension_half.eventually hrelative
  filter_upwards [hdimension, hstar]
    with d hres hcut
  intro r hr hrstar
  try dsimp
  exact hres (saddleSmallRadiusVariable ε r)
    (saddleSmallRadiusVariable_nonneg ε r)
    (hcut r hr hrstar)
end CohnElkies
