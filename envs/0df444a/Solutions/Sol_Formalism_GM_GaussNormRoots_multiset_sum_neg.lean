-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.multiset_sum_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:07.718054+00:00
-- url     : https://prove2.me/submissions/7f254964-38fe-4879-8935-11701b7afca8

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
theorem _root_.solution {α : Type} (m : Multiset α) (f : α → ℝ) :
    (m.map fun x => -f x).sum = -(m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, neg_add]
end Formalism.GM.GaussNormRoots
