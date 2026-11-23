-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_card_gt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:54.801808+00:00
-- url     : https://prove2.me/submissions/e57b333f-9261-47f8-9237-1d0dd84cebea

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
theorem _root_.solution {n k C : ℕ} (sz : Fin k → ℕ) (p : Fin C → ℕ) (hsz : ∀ i, sz i ≤ n) (hp : ∀ c, p c ≤ n)
    (h : (shapeDeg sz : Fin n → ℕ) = shapeDeg p) (j : ℕ) :
    (Finset.univ.filter fun i => j < sz i).card = (Finset.univ.filter fun c => j < p c).card := by
  by_cases hj : j < n
  · exact congrFun h ⟨j, hj⟩
  · rw [Finset.filter_false_of_mem (fun i _ => by have := hsz i; omega),
      Finset.filter_false_of_mem (fun c _ => by have := hp c; omega)]
    rfl
end Formalism.DworkPowerSeriesWeights
