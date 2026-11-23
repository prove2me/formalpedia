-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.shape_count_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:56.277115+00:00
-- url     : https://prove2.me/submissions/0413766d-05e0-4661-96bd-54fa00cd2713

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
theorem _root_.solution {J : Type} [DecidableEq J] {p : ℕ} (τ : Fin p → J)
    (hτ : Function.Injective τ) (j : J) :
    (Finset.univ.filter (fun i => τ i = j)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact hτ (ha.trans hb.symm)
end Formalism.DworkPowerSeriesWeights
