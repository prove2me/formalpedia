-- Prove2me | solution 1 for Formalism.CohomologicalDescent.comb_roots_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:57.141403+00:00
-- url     : https://prove2.me/submissions/4b642758-494b-4305-b11b-0521e84b8764

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ContentLinkageHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution {K : Type} [Field K] {N : ℕ} (f : Fin N → K) :
    (∏ a, (X + C (f a))).roots = Multiset.map (fun a => -f a) Finset.univ.val := by
  have h : (∏ a, (X + C (f a))) =
      ((Multiset.map (fun a => -f a) Finset.univ.val).map fun x => X - C x).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp [sub_eq_add_neg]
  rw [h, Polynomial.roots_multiset_prod_X_sub_C]
end Formalism.CohomologicalDescent
