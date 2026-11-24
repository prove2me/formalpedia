-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.exists_norm_iteratedFDeriv_critCut_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:41.747447+00:00
-- url     : https://prove2.me/submissions/000261dd-b6c1-4021-bb1f-cf987d985e72

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_WhittakerVanishingImpliesZero_critCut_contDiff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
theorem _root_.solution (d : ℕ) {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    ∃ C : ℝ, ∀ x : Fin d → ℂ, ‖iteratedFDeriv ℝ j (critCut δ 0) x‖ ≤ C := by
  have hc : HasCompactSupport (critCut (n := d) δ 0) :=
    HasCompactSupport.intro (isCompact_closedBall 0 (2 * δ)) fun x hx => critCut_eq_zero hδ (by
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
      have e : (x - fun _ => (0 : ℂ)) = x := by funext k; simp
      rw [e]
      exact hx.le)
  exact ((critCut_contDiff δ 0 (n := j)).continuous_iteratedFDeriv le_rfl).bounded_above_of_compact_support
    (hc.iteratedFDeriv j)
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
