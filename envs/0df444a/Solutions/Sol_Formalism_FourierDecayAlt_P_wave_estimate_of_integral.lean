-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.wave_estimate_of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:43:56.664068+00:00
-- url     : https://prove2.me/submissions/420550f3-13f2-433d-86b8-88bafb493657

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
open scoped ComplexOrder
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C.EstWaveOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hG hI hP Kr hK0 Th e ε hε i hi1 hi2 w hw hcnt
  obtain ⟨θ, hθ, hb⟩ := hP ε hε i hi1 hi2 w hw hcnt
  exact ⟨θ, hθ, fun Y hY κ hκ => ⟨(hI ε hε i hi1 hi2 w Y hY κ hκ).2,
    fun l hl hl0 => ⟨S.bigPlaces i l, hb Y hY κ hκ l hl hl0⟩⟩⟩
end Formalism.FourierDecayAlt.P
