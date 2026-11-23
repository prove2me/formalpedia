-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lclosedeq_hw_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:08.921031+00:00
-- url     : https://prove2.me/submissions/04447d97-5846-4503-b0d0-a5aecca49d51

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LClosedeqLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lclosedeq_lpMinor_map
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (hn : n ≤ r) (ν : Fin n → ℕ) :
    map φ (hw R hn ν) = hw S hn ν := by
  simp only [hw, map_prod, map_pow, lclosedeq_lpMinor_map]
end Formalism.GradedWeylDivisibility
