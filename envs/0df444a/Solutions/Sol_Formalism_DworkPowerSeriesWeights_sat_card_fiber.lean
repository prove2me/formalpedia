-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_card_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:01.651112+00:00
-- url     : https://prove2.me/submissions/7dc74446-744c-4c8c-8720-aa595c4fc928

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_card_gt
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_sat_card_split

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
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {n k C : ℕ} (sz : Fin k → ℕ) (p : Fin C → ℕ) (hsz : ∀ i, sz i ≤ n) (hp : ∀ c, p c ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg p) (j : ℕ) :
    Fintype.card {c // p c = j + 1} = Fintype.card {i // sz i = j + 1} := by
  rw [Fintype.card_subtype, Fintype.card_subtype]
  have h1 := sat_card_split sz j
  have h2 := sat_card_split p j
  have h3 := sat_card_gt sz p hsz hp h j
  have h4 := sat_card_gt sz p hsz hp h (j + 1)
  omega
end Formalism.DworkPowerSeriesWeights
