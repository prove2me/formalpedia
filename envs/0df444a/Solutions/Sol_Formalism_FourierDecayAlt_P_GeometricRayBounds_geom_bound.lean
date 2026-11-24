-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GeometricRayBounds.geom_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:08.287962+00:00
-- url     : https://prove2.me/submissions/e9f934de-06b3-4a29-8950-df5c8852cd1e

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragingVanishes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GeometricRayBounds
namespace Formalism.FourierDecayAlt.P.GeometricRayBounds
theorem _root_.solution (q : ℂ) (hq : ‖q‖ = 1) (hq1 : q ≠ 1) (M : ℕ) :
    ‖∑ m ∈ range M, q ^ m‖ ≤ 2 / ‖q - 1‖ := by
  have hne : 0 < ‖q - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hq1)
  rw [geom_sum_eq hq1, norm_div]
  apply div_le_div_of_nonneg_right _ hne.le
  calc ‖q ^ M - 1‖ ≤ ‖q ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      rw [norm_pow, hq, one_pow, norm_one]
      norm_num
end Formalism.FourierDecayAlt.P.GeometricRayBounds
