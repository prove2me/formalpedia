-- Prove2me | solution 1 for CohnElkies.upperFirstBranch_saddleSourceThirdMoment_scaled_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/7ea585b4-a6fb-43a1-9dc8-4eac55186dd2

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperShortShellThirdMoment_le
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds
import Theorems.Thm_CohnElkies_upperFirstBranch_shortVariance_le_gamma
import Theorems.Thm_CohnElkies_saddleSourcePositiveShellThirdMoment_nonneg
import Theorems.Thm_CohnElkies_upperPositiveShellThirdMoment_firstBranch_le
import Theorems.Thm_CohnElkies_upperGammaVariance_firstBranch_scaled_le
import Theorems.Thm_CohnElkies_upperGammaThirdMoment_firstBranch_scaled_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hscale : 1 ≤ ℓ * (1 + u)) :
    (1 + u) ^ 2 * upperSaddleThirdMoment ε ℓ (u - 1) ≤
      saddleSourceFirstBranchThirdMomentCoefficient ε := by
  let η : ℝ := 1 + u
  let U : ℝ := 2 + ε / 2
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hU : 0 < U := by
    try dsimp [U]
    positivity
  have hηU : η ≤ U := by
    try dsimp [η, U]
    linarith
  have hA : 0 ≤ shortEndpoint ε := by
    have hcut : 0 < shortCutoff ε := by
      unfold shortCutoff
      positivity
    exact (hcut.trans_le horder).le
  have hgamma := upperGammaVariance_firstBranch_scaled_le
    hℓ hη (by simpa [η] using! hscale)
  have hthirdgamma := upperGammaThirdMoment_firstBranch_scaled_le
    hℓ hη (by simpa [η] using! hscale)
  have hgammanonneg : 0 ≤ upperGammaVariance ℓ η :=
    (show 0 ≤ 1 / (2 * η) by positivity).trans
      (upperGammaVariance_bounds hℓ hη).1
  have hshortvariance :=
    upperFirstBranch_shortVariance_le_gamma
      hε hεsmall hℓ hulower huupper horder hmargin
  have hshortvariance' :
      upperShortShellVariance ε (u - 1) ≤
        upperGammaVariance ℓ η := by
    try dsimp [η]
    nlinarith [mul_nonneg hε.le hgammanonneg]
  have hshortthird := upperShortShellThirdMoment_le
    (δ := u - 1) hε horder hmargin
  have hshort :
      η ^ 2 * upperShortShellThirdMoment ε (u - 1) ≤
        (3 / 2 : ℝ) * shortEndpoint ε * U := by
    calc
      η ^ 2 * upperShortShellThirdMoment ε (u - 1) ≤
          η ^ 2 *
            (shortEndpoint ε *
              upperShortShellVariance ε (u - 1)) :=
        mul_le_mul_of_nonneg_left hshortthird (sq_nonneg η)
      _ ≤ η ^ 2 *
          (shortEndpoint ε * upperGammaVariance ℓ η) := by
        gcongr
      _ = shortEndpoint ε * η *
          (η * upperGammaVariance ℓ η) := by ring
      _ ≤ shortEndpoint ε * η * (3 / 2 : ℝ) := by
        gcongr
      _ ≤ shortEndpoint ε * U * (3 / 2 : ℝ) := by
        gcongr
      _ = (3 / 2 : ℝ) * shortEndpoint ε * U := by
        ring
  have hremote :=
    upperPositiveShellThirdMoment_firstBranch_le
      hε hulower huupper
  have hremote0 :=
    saddleSourcePositiveShellThirdMoment_nonneg
      hε (ε / 2)
  have hremoteScaled :
      η ^ 2 * upperPositiveShellThirdMoment ε (u - 1) ≤
        U ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) := by
    calc
      η ^ 2 * upperPositiveShellThirdMoment ε (u - 1) ≤
          η ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) :=
        mul_le_mul_of_nonneg_left hremote (sq_nonneg η)
      _ ≤ U ^ 2 * upperPositiveShellThirdMoment ε (ε / 2) := by
        gcongr
  unfold saddleSourceFirstBranchThirdMomentCoefficient
  unfold upperSaddleThirdMoment upperNetShellThirdMoment
  have hargument : 2 + (u - 1) = η := by
    try dsimp [η]
    ring
  rw [hargument]
  change η ^ 2 *
      (upperGammaThirdMoment ℓ η +
        (upperPositiveShellThirdMoment ε (u - 1) +
          upperShortShellThirdMoment ε (u - 1))) ≤
    (5 / 2 : ℝ) +
      (3 / 2 : ℝ) * shortEndpoint ε * U +
      U ^ 2 * upperPositiveShellThirdMoment ε (ε / 2)
  nlinarith
end CohnElkies
