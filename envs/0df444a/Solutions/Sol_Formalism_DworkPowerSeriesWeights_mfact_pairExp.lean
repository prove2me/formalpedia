-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.mfact_pairExp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:57:10.5688+00:00
-- url     : https://prove2.me/submissions/ab0889a9-45e7-4b7c-8f81-f386562cb32e

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_eq_prod_univ
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_pairExp_apply

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
theorem _root_.solution {ι : Type} [Fintype ι] (n : ι → ℕ) :
    mfact (pairExp n) = (∏ i, (n i).factorial) * ∏ i, (n i).factorial := by
  classical
  rw [mfact_eq_prod_univ, Fintype.prod_prod_type, Fintype.prod_bool]
  simp only [pairExp_apply]
end Formalism.DworkPowerSeriesWeights
