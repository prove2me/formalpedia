-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.multiset_card_filter_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:07.840367+00:00
-- url     : https://prove2.me/submissions/efff8e42-0152-4227-8283-c3fb73cd0e1a

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
open Formalism.GM.GaussNormRoots
namespace Formalism.GM.GaussNormRoots
theorem _root_.solution {α : Type} (m : Multiset α) (P : α → Prop) [DecidablePred P] :
    ((m.filter P).card : ℝ) = (m.map fun x => if P x then (1 : ℝ) else 0).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    by_cases h : P a
    · rw [Multiset.filter_cons_of_pos _ h]
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons, h, if_true]
      push_cast
      rw [ih]
      ring
    · rw [Multiset.filter_cons_of_neg _ h]
      simp only [Multiset.map_cons, Multiset.sum_cons, h, if_false]
      rw [ih]
      ring
end Formalism.GM.GaussNormRoots
