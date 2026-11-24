-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_norm_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:09.428022+00:00
-- url     : https://prove2.me/submissions/0b62db68-0959-4f1d-b414-a92a43ea52e1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {d : ℕ} (L : (Fin d → ℂ) →L[ℂ] ℂ) : ‖L‖ ≤ ∑ l, ‖L (Pi.single l 1)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun v => ?_
  have hv : v = ∑ l, v l • (Pi.single l (1 : ℂ) : Fin d → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Pi.single_smul]; simp
  conv_lhs => rw [hv]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v l) (norm_nonneg _)
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
