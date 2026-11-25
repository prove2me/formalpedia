-- Prove2me | solution 1 for Formalism.REAL.norm_entry_mul_near_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:33.70075+00:00
-- url     : https://prove2.me/submissions/9f3f6ef4-3e05-450f-96ed-8cda0f90d49d

import Definitions.Def_Formalism_RealPlaceAnalysis_InstMeasurableSpaceUJ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PlaceRankTwoOne
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Theorems.Thm_Formalism_REAL_frobenius_eq_norm_sq
import Theorems.Thm_Formalism_REAL_norm_le_of_near_one
import Theorems.Thm_Formalism_REAL_f1auxiliary_entry_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Metric Kronecker
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.frobeniusNormedAddCommGroup
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} {g u : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hg : hs g ≤ R ^ 2) (hu : hs (u - 1) < 1 / 4) (i j : Fin n) :
    ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  have hg' : ‖g‖ ≤ R := by
    rw [frobenius_eq_norm_sq] at hg
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 hg
  have hu' := norm_le_of_near_one hu
  have he : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have := f1auxiliary_entry_le (g * u) i j
    rw [frobenius_eq_norm_sq] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  calc ‖(g * u) i j‖ ≤ ‖g * u‖ := he
    _ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
    _ ≤ R * (Real.sqrt n + 1 / 2) := by gcongr
    _ ≤ R * (Real.sqrt n + 1) := by gcongr; norm_num
end Formalism.REAL
