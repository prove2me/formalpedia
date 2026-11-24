-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.top_density_of_averaging
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:14.480033+00:00
-- url     : https://prove2.me/submissions/4a24d62b-b606-491b-81f8-f85448e2d24b

import Definitions.Def_Formalism_HermitianCurvature_LemmaDensOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InnerDensityOfAveraging

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.DensityAveraging.DensStepTopOfAvg := by
  rintro ⟨C0, hI⟩ hAvg
  refine ⟨C0, ?_⟩
  intro CV hCV k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ H hrel hG hc hMore
  obtain ⟨S, hS⟩ := hI CV hCV k r Wp Wq D A ε mm F' γ H hrel hG hc
  obtain ⟨C', x₁, hb⟩ := hS hMore
  exact S.tie (hAvg S.β S.β_ne S.V S.p S.s S.w S.a C' x₁ S.w_inj hb S.k₀)
end Formalism.FourierDecayAlt.P
