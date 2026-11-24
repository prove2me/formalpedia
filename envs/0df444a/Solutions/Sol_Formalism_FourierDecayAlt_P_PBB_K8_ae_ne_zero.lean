-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBB.K8.ae_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:08:35.575038+00:00
-- url     : https://prove2.me/submissions/f9299eba-7658-4e69-9240-86a34508f3c1

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramLocTendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Real NumberField
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBB Formalism.FourierDecayAlt.P.PBB.K8
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBB.K8
theorem _root_.solution : ∀ᵐ c : ℂ ∂volume, c ≠ 0 := by
  simp [ae_iff]
end Formalism.FourierDecayAlt.P.PBB.K8
