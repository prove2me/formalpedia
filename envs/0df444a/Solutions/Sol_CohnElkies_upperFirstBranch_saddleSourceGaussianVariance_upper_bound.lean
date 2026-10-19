-- Prove2me | solution 1 for CohnElkies.upperFirstBranch_saddleSourceGaussianVariance_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/5c2809a6-c3e5-4e3d-aae6-1e99b362459e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperShortShellVariance_nonneg
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds
import Theorems.Thm_CohnElkies_saddleSourcePositiveShellVariance_nonneg
import Theorems.Thm_CohnElkies_upperPositiveShellVariance_firstBranch_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hscale : 1 ≤ ℓ * (1 + u)) :
    saddleSourceGaussianVariance ε ℓ u ≤
      ((3 / 2 : ℝ) +
          (2 + ε / 2) *
            upperPositiveShellVariance ε (ε / 2)) /
        (1 + u) := by
  let η : ℝ := 1 + u
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have hηupper : η ≤ 2 + ε / 2 := by
    try dsimp [η]
    linarith
  have hgammabound :=
    (upperGammaVariance_bounds hℓ hη).2
  have hsmallterm : 1 / (ℓ * η ^ 2) ≤ 1 / η := by
    rw [div_le_div_iff₀ (by positivity : 0 < ℓ * η ^ 2) hη]
    try dsimp [η] at hscale ⊢
    nlinarith [hscale]
  have hgamma : upperGammaVariance ℓ η ≤
      (3 / 2 : ℝ) / η := by
    calc
      upperGammaVariance ℓ η ≤
          1 / (2 * η) + 1 / (ℓ * η ^ 2) := hgammabound
      _ ≤ 1 / (2 * η) + 1 / η := by gcongr
      _ = (3 / 2 : ℝ) / η := by ring_nf
  have hshort := upperShortShellVariance_nonneg
    (δ := u - 1) hε horder hmargin
  have hremote := upperPositiveShellVariance_firstBranch_le
    hε hulower huupper
  have hpositive :=
    saddleSourcePositiveShellVariance_nonneg ε (ε / 2)
  have hvariance :
      saddleSourceGaussianVariance ε ℓ u ≤
        (3 / 2 : ℝ) / η +
          upperPositiveShellVariance ε (ε / 2) := by
    unfold saddleSourceGaussianVariance
      upperSaddleVariance upperNetShellVariance
    have hargument : 2 + (u - 1) = η := by
      try dsimp [η]
      ring
    rw [hargument]
    linarith
  calc
    saddleSourceGaussianVariance ε ℓ u ≤
      (3 / 2 : ℝ) / η +
        upperPositiveShellVariance ε (ε / 2) := hvariance
    _ ≤ ((3 / 2 : ℝ) +
          (2 + ε / 2) *
            upperPositiveShellVariance ε (ε / 2)) / η := by
      apply (le_div_iff₀ hη).mpr
      field_simp
      nlinarith [
        mul_nonneg hpositive
          (show 0 ≤ (2 + ε / 2) - η by linarith)]
    _ = ((3 / 2 : ℝ) +
          (2 + ε / 2) *
            upperPositiveShellVariance ε (ε / 2)) /
          (1 + u) := by rfl
end CohnElkies
