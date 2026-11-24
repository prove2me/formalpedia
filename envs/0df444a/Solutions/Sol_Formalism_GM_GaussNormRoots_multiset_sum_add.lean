-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.multiset_sum_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:07.700813+00:00
-- url     : https://prove2.me/submissions/b7bbbbbb-d50d-4020-8dda-4173086103dd

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
theorem _root_.solution {α : Type} (m : Multiset α) (f g : α → ℝ) :
    (m.map fun x => f x + g x).sum = (m.map f).sum + (m.map g).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih]
    ring
end Formalism.GM.GaussNormRoots
