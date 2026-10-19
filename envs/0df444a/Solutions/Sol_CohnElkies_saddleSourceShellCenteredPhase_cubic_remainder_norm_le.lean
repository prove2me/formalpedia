-- Prove2me | solution 1 for CohnElkies.saddleSourceShellCenteredPhase_cubic_remainder_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/c8670501-29a6-4108-af70-f7b3444fdd6e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSourcePositiveShellQuadraticRemainder_norm_le
import Theorems.Thm_CohnElkies_saddleSourceShortShellQuadraticRemainder_norm_le
import Theorems.Thm_CohnElkies_saddleSourceShellQuadraticRemainder_eq

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
    {ε ℓ : ℝ}
    (hε : 0 < ε)
    (hℓ : 0 ≤ ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    (u T : ℝ) :
    ‖saddleSourceShellCenteredPhase ε ℓ u T +
        ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
          T ^ 2 : ℝ) : ℂ)‖ ≤
      (ℓ * upperNetShellThirdMoment ε (u - 1) / 6) *
        |T| ^ 3 := by
  have hshort :=
    saddleSourceShortShellQuadraticRemainder_norm_le
      hε horder hmargin u T
  have hpositive :=
    saddleSourcePositiveShellQuadraticRemainder_norm_le
      hε u T
  have hsum :
      ‖saddleSourceShellQuadraticRemainder ε u T‖ ≤
        (|T| ^ 3 / 6) *
          upperNetShellThirdMoment ε (u - 1) := by
    unfold saddleSourceShellQuadraticRemainder
      upperNetShellThirdMoment
    calc
      ‖(∫ a in shortCutoff ε..shortEndpoint ε,
          (shortShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T) +
        (∫ a in shellLocation ε..shellLocation ε + 1,
          (positiveShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T)‖ ≤
        ‖∫ a in shortCutoff ε..shortEndpoint ε,
          (shortShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T‖ +
        ‖∫ a in shellLocation ε..shellLocation ε + 1,
          (positiveShellDensity ε a : ℂ) *
            saddleSourceCosineQuadraticRemainder a u T‖ :=
          norm_add_le _ _
      _ ≤ (|T| ^ 3 / 6) *
          upperShortShellThirdMoment ε (u - 1) +
        (|T| ^ 3 / 6) *
          upperPositiveShellThirdMoment ε (u - 1) :=
          add_le_add hshort hpositive
      _ = (|T| ^ 3 / 6) *
          (upperPositiveShellThirdMoment ε (u - 1) +
            upperShortShellThirdMoment ε (u - 1)) := by
          ring
  have heq :
      saddleSourceShellCenteredPhase ε ℓ u T +
          ((ℓ * upperNetShellVariance ε (u - 1) / 2 *
            T ^ 2 : ℝ) : ℂ) =
        (ℓ : ℂ) *
          saddleSourceShellQuadraticRemainder ε u T := by
    rw [saddleSourceShellQuadraticRemainder_eq
      hε horder u T]
    unfold saddleSourceShellCenteredPhase
    push_cast
    ring
  rw [heq, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hℓ]
  calc
    ℓ * ‖saddleSourceShellQuadraticRemainder ε u T‖ ≤
      ℓ * ((|T| ^ 3 / 6) *
        upperNetShellThirdMoment ε (u - 1)) :=
        mul_le_mul_of_nonneg_left hsum hℓ
    _ = (ℓ * upperNetShellThirdMoment ε (u - 1) / 6) *
      |T| ^ 3 := by
      ring
end CohnElkies
