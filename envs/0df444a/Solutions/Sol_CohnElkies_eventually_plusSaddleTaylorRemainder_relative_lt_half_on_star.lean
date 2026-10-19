-- Prove2me | solution 1 for CohnElkies.eventually_plusSaddleTaylorRemainder_relative_lt_half_on_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/eb400407-270d-4597-a849-9a89d76fe896

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSmallRadiusVariable_nonneg
import Theorems.Thm_CohnElkies_exists_eventually_y_star_le_log_eighth_add
import Theorems.Thm_CohnElkies_eventually_saddleSmallResidueTruncation_succ_double_le
import Theorems.Thm_CohnElkies_tendsto_saddleResidue_dimension_half
import Theorems.Thm_CohnElkies_eventually_saddleNegative_relativeGammaTail_lt_half
import Theorems.Thm_CohnElkies_saddleNegativeRelativeCoefficient_nonneg
import Theorems.Thm_CohnElkies_plusSaddleTaylorRemainder_negativeContour_relative_bound
import Theorems.Thm_CohnElkies_exists_saddleNegativeContourPhaseError_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a) :
    ∀ᶠ d : ℕ in atTop,
      ∀ r : ℝ, 0 < r → r ≤ saddleSmallRadiusStar ε d →
        let ℓ : ℝ := (d : ℝ) / 2
        let N : ℕ := saddleSmallResidueTruncation ℓ
        let y : ℝ := saddleSmallRadiusVariable ε r
        Real.exp y *
          ‖plusSaddleTaylorRemainder ε ℓ N r /
            (saddleOriginValue ε ℓ : ℂ)‖ < 1 / 2 := by
  obtain ⟨C, hC, hstar⟩ :=
    exists_eventually_y_star_le_log_eighth_add hε horder
  obtain ⟨K, hK, hphase⟩ :=
    exists_saddleNegativeContourPhaseError_bound hε horder
  let Kε : ℝ := saddleNegativeRelativeCoefficient ε
  have hKε : 0 ≤ Kε :=
    saddleNegativeRelativeCoefficient_nonneg hε
  have htail := eventually_saddleNegative_relativeGammaTail_lt_half
    hε C K Kε hC hK hKε
  have htaildim :=
    tendsto_saddleResidue_dimension_half.eventually htail
  have hdepth :=
    tendsto_saddleResidue_dimension_half.eventually
      eventually_saddleSmallResidueTruncation_succ_double_le
  filter_upwards [hstar, htaildim, hdepth,
    eventually_gt_atTop (0 : ℕ)] with d hcut htaild hNd hd
  intro r hr hrstar
  try dsimp
  let ℓ : ℝ := (d : ℝ) / 2
  let N : ℕ := saddleSmallResidueTruncation ℓ
  let y : ℝ := saddleSmallRadiusVariable ε r
  have hℓ : 0 < ℓ := by
    try dsimp [ℓ]
    positivity
  have hy : 0 ≤ y := saddleSmallRadiusVariable_nonneg ε r
  have hyupper : y ≤ Real.log ℓ / 8 + C := by
    exact hcut r hr.le hrstar
  have hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ := hNd
  have hrelative :=
    plusSaddleTaylorRemainder_negativeContour_relative_bound
      hε hεsmall hℓ N hN horder hmargin hr
  have herr := hphase ℓ hℓ N hN
  have herror :
      saddleNegativeContourPhaseError ε ℓ N ≤
        K * (2 * (N : ℝ) + 1) ^ 2 / ℓ := by
    exact (le_abs_self _).trans herr
  have htarget := htaild y hy hyupper
  change
    Real.exp y *
      ‖plusSaddleTaylorRemainder ε ℓ N r /
        (saddleOriginValue ε ℓ : ℂ)‖ < 1 / 2
  calc
    Real.exp y *
      ‖plusSaddleTaylorRemainder ε ℓ N r /
        (saddleOriginValue ε ℓ : ℂ)‖ ≤
      Real.exp y *
        (Kε * Real.sqrt y * y ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp (saddleNegativeContourPhaseError ε ℓ N)) := by
      gcongr
    _ ≤ Real.exp y *
        (Kε * Real.sqrt y * y ^ N /
          Real.Gamma ((N : ℝ) + 3 / 2) *
            Real.exp
              (K * (2 * (N : ℝ) + 1) ^ 2 / ℓ)) := by
      gcongr
    _ < 1 / 2 := htarget
end CohnElkies
