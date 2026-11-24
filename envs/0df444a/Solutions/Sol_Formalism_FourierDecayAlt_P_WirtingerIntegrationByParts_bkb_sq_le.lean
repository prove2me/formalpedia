-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:05.799205+00:00
-- url     : https://prove2.me/submissions/15861062-c42e-4dd1-90ca-014c32ccb513

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_norm_le_sum

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
theorem _root_.solution {d : ℕ} (L : (Fin d → ℂ) →L[ℂ] ℂ) :
    ‖L‖ ^ 2 ≤ d * ∑ l, Complex.normSq (L (Pi.single l 1)) := by
  have h1 := bkb_norm_le_sum L
  have h2 : (∑ l, ‖L (Pi.single l 1)‖) ^ 2 ≤ ((Finset.univ : Finset (Fin d)).card : ℝ) * ∑ l, ‖L (Pi.single l 1)‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  simp only [Complex.normSq_eq_norm_sq]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
