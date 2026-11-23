-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.shape_count_total
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:00.298794+00:00
-- url     : https://prove2.me/submissions/db4ab6e9-23a2-4d07-b4f9-e2057e5ef398

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementH
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MinorProductSupportTop

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
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {J : Type} [Fintype J] [DecidableEq J] {p : ℕ} (τ : Fin p → J) :
    (∑ j, (Finset.univ.filter (fun i => τ i = j)).card) = p := by
  have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin p)))
    (t := Finset.univ) (f := τ) (fun i _ => Finset.mem_coe.mpr (Finset.mem_univ (τ i)))
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm
end Formalism.DworkPowerSeriesWeights
