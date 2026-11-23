-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.multiset_prod_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:06.553025+00:00
-- url     : https://prove2.me/submissions/d55f3747-3224-4220-9e09-2c2de7d9a14e

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
theorem _root_.solution {α : Type} (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    0 < (m.map f).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact mul_pos (hf a) ih
end Formalism.GM.GaussNormRoots
