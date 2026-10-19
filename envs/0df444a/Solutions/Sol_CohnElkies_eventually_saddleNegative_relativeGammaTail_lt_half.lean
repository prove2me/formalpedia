-- Prove2me | solution 1 for CohnElkies.eventually_saddleNegative_relativeGammaTail_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.981105+00:00
-- url     : https://prove2.me/submissions/3e2f3910-33ad-4a02-a016-0e06b1a784d1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleNegative_relativeGammaTail_le_majorant
import Theorems.Thm_CohnElkies_tendsto_saddleNegativeRelativeGammaTailMajorant

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ} (hε : 0 < ε)
    (C K Kε : ℝ)
    (hC : 0 ≤ C)
    (hK : 0 ≤ K)
    (hKε : 0 ≤ Kε) :
    ∀ᶠ ℓ : ℝ in atTop,
      ∀ y : ℝ,
        0 ≤ y → y ≤ Real.log ℓ / 8 + C →
          Real.exp y *
            (Kε * Real.sqrt y *
              y ^ saddleSmallResidueTruncation ℓ /
                Real.Gamma
                  ((saddleSmallResidueTruncation ℓ : ℝ) + 3 / 2) *
              Real.exp
                (K *
                  (2 * (saddleSmallResidueTruncation ℓ : ℝ) + 1) ^ 2 /
                    ℓ)) < 1 / 2 := by
  have _hε : 0 < ε := hε
  have _hK : 0 ≤ K := hK
  have hmajor :=
    (tendsto_saddleNegativeRelativeGammaTailMajorant C K Kε).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hmajor, eventually_ge_atTop (1 : ℝ)]
    with ℓ hsmall hℓ
  intro y hy hyupper
  exact (saddleNegative_relativeGammaTail_le_majorant
    hKε hC hℓ hy hyupper).trans_lt hsmall
end CohnElkies
