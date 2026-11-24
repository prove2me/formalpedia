-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.logb_multiset_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:53.885809+00:00
-- url     : https://prove2.me/submissions/3dd6ef98-8e36-48e7-9680-49d6c77850b8

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
import Theorems.Thm_Formalism_GM_GaussNormRoots_multiset_prod_pos

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
theorem _root_.solution {α : Type} (b : ℝ) (m : Multiset α) (f : α → ℝ) (hf : ∀ x, 0 < f x) :
    Real.logb b (m.map f).prod = (m.map fun x => Real.logb b (f x)).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [Real.logb_mul (hf a).ne' (multiset_prod_pos m f hf).ne', ih]
end Formalism.GM.GaussNormRoots
