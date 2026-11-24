-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.mfact_mul_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:56:02.730158+00:00
-- url     : https://prove2.me/submissions/bb86d3ef-7907-4d80-b4a1-4d4ce18898f2

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_mfact_eq_prod_univ

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
theorem _root_.solution {σ : Type} [Fintype σ] (μ ν : σ →₀ ℕ) :
    mfact μ * mfact ν ∣ mfact (μ + ν) := by
  rw [mfact_eq_prod_univ, mfact_eq_prod_univ, mfact_eq_prod_univ, ← Finset.prod_mul_distrib]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun x _ =>
    Nat.factorial_mul_factorial_dvd_factorial_add _ _
end Formalism.DworkPowerSeriesWeights
