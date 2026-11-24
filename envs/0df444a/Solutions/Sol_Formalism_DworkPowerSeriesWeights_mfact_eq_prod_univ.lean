-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.mfact_eq_prod_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:43:37.037388+00:00
-- url     : https://prove2.me/submissions/dd67559d-cd23-493e-9253-7406ca7f044e

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {σ : Type} [Fintype σ] (κ : σ →₀ ℕ) :
    mfact κ = ∏ x, (κ x).factorial := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => rfl)
end Formalism.DworkPowerSeriesWeights
