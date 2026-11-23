-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_glue_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:55.160542+00:00
-- url     : https://prove2.me/submissions/e5a0181d-8ee2-4e52-b6d9-a8979a71a3c4

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation

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
theorem _root_.solution {S τ σ : Type} [Fintype S] [DecidableEq S] (e : S → τ → σ)
    (he : ∀ s t v w, e s v = e t w → s = t ∧ v = w) (m : S → τ →₀ ℕ) (s : S) (v : τ) :
    (∑ t, (m t).mapDomain (e t)) (e s v) = m s v := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply (fun x y h => (he s s x y h).2) _ _
  · intro t _ hts
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨w, hw⟩
    exact hts (he t s w v hw).1
  · intro h; exact absurd (Finset.mem_univ s) h
end Formalism.DworkPowerSeriesWeights
