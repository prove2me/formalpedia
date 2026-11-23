-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3.hk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:13:57.006903+00:00
-- url     : https://prove2.me/submissions/9474e25d-16ee-4480-aa3b-80073307e2e6

import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalVolumePositivity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentBlockMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormNormLemmas Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.PN
open Finset
open Classical
namespace Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
theorem _root_.solution {c t m5 f : ℝ} (hc : 0 ≤ c) (hf : 0 ≤ f) (ht : t ≤ m5) : c * (f * t) ≤ c * (m5 * f) := by
  rw [mul_comm m5 f]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht hf) hc
end Formalism.FourierDecayAlt.P.HermitianFormNormLemmas.D3
