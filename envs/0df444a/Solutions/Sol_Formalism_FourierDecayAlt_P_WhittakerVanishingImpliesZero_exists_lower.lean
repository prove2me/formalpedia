-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero.exists_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:13.598837+00:00
-- url     : https://prove2.me/submissions/6f4e0527-8871-4e4a-a171-4c3ce49d8c62

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero

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
theorem _root_.solution {Kc : Set ℂ} (hK : IsCompact Kc) (h0 : (0 : ℂ) ∉ Kc) :
    ∃ d : ℝ, 0 < d ∧ ∀ D ∈ Kc, d ≤ ‖D‖ := by
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl 0 h0
  refine ⟨d, hd, fun D hDK => ?_⟩
  by_contra hlt
  exact hball (by simpa [Metric.mem_ball] using not_le.mp hlt) hDK
end Formalism.FourierDecayAlt.P.WhittakerVanishingImpliesZero
